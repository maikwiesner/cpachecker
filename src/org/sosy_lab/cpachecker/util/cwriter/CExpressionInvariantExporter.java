// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.util.cwriter;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.IO;
import org.sosy_lab.common.io.PathTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.FileLocation;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smt.Solver;
import org.sosy_lab.cpachecker.util.predicates.weakening.InductiveWeakeningManager;
import org.sosy_lab.cpachecker.util.predicates.weakening.WeakeningOptions;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;

@Options(prefix = "cinvariants")
public class CExpressionInvariantExporter {

  @Option(secure = true, description = "Attempt to simplify the invariant before "
      + "exporting [may be very expensive].")
  private boolean simplify = false;

  @Option(secure = true, description = "Write invariants for given lines to additional file."
      + "Empty list (\"[]\") means all lines are exported")

  private String exportPlainForLines = null;
  private Set<Integer> plainInvLineNumbers;
  private boolean allLines;

  private static final String BEFORE_TOKEN = "-";
  private static final String AFTER_TOKEN = "+";
  /**
   * This map specifies for each line for which an invariant was computed its relative
   * position to that line, i.e. whether the invariant holds before or after that line.
   * The value string is always either {@link #BEFORE_TOKEN} or {@link #AFTER_TOKEN}
   */
  private Map<Integer, String> invariantPosMap;

  private final PathTemplate prefix;

  private final FormulaManagerView fmgr;
  private final BooleanFormulaManager bfmgr;
  private final FormulaToCExpressionConverter formulaToCExpressionConverter;
  private final InductiveWeakeningManager inductiveWeakeningManager;

  /*TODO: maybe completely seperate generation of invariant file from this
      and create an extra class for that */

  public CExpressionInvariantExporter(
      Configuration pConfiguration,
      LogManager pLogManager,
      ShutdownNotifier pShutdownNotifier,
      PathTemplate pPrefix)
      throws InvalidConfigurationException {
    pConfiguration.inject(this);
    prefix = pPrefix;
    @SuppressWarnings("resource")
    Solver solver = Solver.create(pConfiguration, pLogManager, pShutdownNotifier);
    fmgr = solver.getFormulaManager();
    bfmgr = fmgr.getBooleanFormulaManager();
    formulaToCExpressionConverter = new FormulaToCExpressionConverter(fmgr);
    inductiveWeakeningManager =
        new InductiveWeakeningManager(
            new WeakeningOptions(pConfiguration), solver, pLogManager, pShutdownNotifier);

    //initialize plain export of invariants if activated
    if (exportPlainForLines != null) {
      initPlainInvariantsExport(pLogManager);
    }

  }

  /**
   * creates output file for exported invariants and initializes necessary fields
   *
   * @param pLogManager used for logging
   */
  private void initPlainInvariantsExport(LogManager pLogManager) {
    try {
    /* PrintWriter will create a new file or delete its contents if its already exists.
     Either way an empty target file for plain invariants get created */
      new PrintWriter(prefix.getPath("plain.txt").toString()).close();
    } catch (FileNotFoundException e) {
      pLogManager.log(Level.WARNING, "could not create file for plain invariants.");
      //deactivate export of invariants as target file could not be created
      exportPlainForLines = null;
    }

    if (exportPlainForLines != null) {

      //initialize map
      invariantPosMap = new HashMap<>();

      //parse #exportPlainForLines argument
      //check that first and last character are '[' and ']'
      if (exportPlainForLines.charAt(0) != '['
          || exportPlainForLines.charAt(exportPlainForLines.length() - 1) != ']') {
        pLogManager.log(Level.WARNING, "invalid value for cinvariants.exportPlainForLines");
      } else if (exportPlainForLines.equals("[]")) {
        allLines = true;
      } else {
        allLines = false;
        plainInvLineNumbers = new HashSet<>();

        String lineNumberList =
            exportPlainForLines.substring(1, exportPlainForLines.length() - 1);
        String[] lineNumbers = lineNumberList.split(",");
        for (String lineNumber : lineNumbers) {
          //ingore leading and trailing whitespace
          String lineNumberTrimmed = lineNumber.trim();
          if (lineNumberTrimmed.contains("-")) {
            //this string describes an interval
            String[] bounds = lineNumberTrimmed.split("-");
            //there should be two values (lower and upper bound)
            if (bounds.length != 2) {
              //print warning and skip this string
              pLogManager.log(Level.WARNING,
                  "could not parse range " + lineNumberTrimmed + ", skipping!");
              continue;
            }

            int lowerBound = 0;
            int upperBound = 0;
            try {
              lowerBound = Integer.parseInt(bounds[0]);
              upperBound = Integer.parseInt(bounds[1]);
            } catch (NumberFormatException e) {
              //print waring and skip this string
              pLogManager.log(Level.WARNING,
                  "could not parse range " + lineNumberTrimmed + ", skipping!");
              continue;
            }
            //add each value of range to set
            for (int value = lowerBound; value <= upperBound; value++) {
              plainInvLineNumbers.add(value);
            }

          } else {
            //add single value to set
            try {
              plainInvLineNumbers.add(Integer.parseInt(lineNumberTrimmed));
            } catch (NumberFormatException e) {
              //print warning and ignore this value
              pLogManager.log(Level.WARNING,
                  "could not parse line number " + lineNumberTrimmed + ", skipping!");
            }
          }
        }
      }
    }
  }


  /**
   * Export invariants extracted from {@code pReachedSet} into the file specified by the options as
   * {@code __VERIFIER_assume()} calls, intermixed with the program source code.
   */
  public void exportInvariant(CFA pCfa, UnmodifiableReachedSet pReachedSet)
      throws IOException, InterruptedException, SolverException {

    for (Path program : pCfa.getFileNames()) {
      // Grab only the last component of the program filename.
      Path trimmedFilename = program.getFileName();
      if (trimmedFilename != null) {
        try (Writer output =
                 IO.openOutputFile(
                     prefix.getPath(trimmedFilename.toString()), Charset.defaultCharset())) {
          writeProgramWithInvariants(output, program, pReachedSet);
        }
      }
    }
  }

  private void writeProgramWithInvariants(
      Appendable out, Path filename, UnmodifiableReachedSet pReachedSet)
      throws IOException, InterruptedException, SolverException {

    Map<Integer, BooleanFormula> reporting = getInvariantsForFile(pReachedSet, filename);

    int lineNo = 0;
    String line;
    try (BufferedReader reader = Files.newBufferedReader(filename)) {
      while ((line = reader.readLine()) != null) {

        Optional<String> invariant = getInvariantForLine(lineNo, reporting);
        if (invariant.isPresent()) {
          String invStr = invariant.orElseThrow();
          out.append("__VERIFIER_assume(").append(invStr).append(");\n");


          //check if invariant should be also exported raw
          if (exportAsPlain(lineNo)) {
            exportPlainInvariantForLine(lineNo, invStr);
          }
        }
        out.append(line)
            .append('\n');
        lineNo++;
      }
    }

  }

  private Optional<String> getInvariantForLine(int lineNo, Map<Integer, BooleanFormula> reporting)
      throws InterruptedException, SolverException {
    BooleanFormula formula = reporting.get(lineNo);
    if (formula == null) {
      return Optional.empty();
    }
    if (simplify) {
      formula = simplifyInvariant(formula);
    }
    return Optional.of(formulaToCExpressionConverter.formulaToCExpression(formula));
  }

  /**
   * Return mapping from line numbers to states associated with the given line.
   */
  private Map<Integer, BooleanFormula> getInvariantsForFile(
      UnmodifiableReachedSet pReachedSet, Path filename) {

    // One formula per reported state.
    Multimap<Integer, BooleanFormula> byState = HashMultimap.create();

    for (AbstractState state : pReachedSet) {

      CFANode loc = AbstractStates.extractLocation(state);
      if (loc != null && loc.getNumEnteringEdges() > 0) {
        CFAEdge edge = loc.getEnteringEdge(0);
        FileLocation location = edge.getFileLocation();

        if (location.getFileName().equals(filename)) {
          BooleanFormula reported = AbstractStates.extractReportedFormulas(fmgr, state);
          if (!bfmgr.isTrue(reported)) {


            setRelativeInvariantPosition(loc, location.getStartingLineInOrigin());

            byState.put(location.getStartingLineInOrigin(), reported);
          }
        }
      }
    }
    return Maps.transformValues(
        byState.asMap(), invariants -> bfmgr.or(invariants)
    );
  }

  /**
   * This method adds an entry to {@link #invariantPosMap}, which specifies the relative location
   * of the invariant to the line number of the node. This has to be done as in some cases the same
   * source line spans over mutltiple CFA blocks, such that the source line number for an invariant
   * can be ambiguous and the different blocks can not be differentiated anymore.
   *
   * @param node   CFA node of the state where invariant holds
   * @param inLine starting line of an entry edge of #node, i.e.
   *               #node.getEnteringEdge(0).getFileLocation().getStartingLineInOrigin();
   */
  private void setRelativeInvariantPosition(CFANode node, int inLine) {
    //check if invariant holds before or after location
    if (node.getNumLeavingEdges() > 0) {
      CFAEdge outEdge = node.getLeavingEdge(0);
      FileLocation outLocation = outEdge.getFileLocation();
      int outLine = outLocation.getStartingLineInOrigin();
      if (inLine == outLine) {
        //invariant holds before #inLine
        invariantPosMap.put(inLine, BEFORE_TOKEN);
      } else {
        //invariant holds after #inLine
        invariantPosMap.put(inLine, AFTER_TOKEN);
      }
    } else {
      //invariant holds after #inLine
      invariantPosMap.put(inLine, AFTER_TOKEN);
    }
  }

  private BooleanFormula simplifyInvariant(BooleanFormula pInvariant)
      throws InterruptedException, SolverException {
    return inductiveWeakeningManager.removeRedundancies(pInvariant);
  }

  /**
   * specifies if invariant for given line should be additionally exported
   *
   * @param line source code line
   * @return true iff invariant for line should be exported, false otherwise
   */
  private boolean exportAsPlain(int line) {
    return allLines || plainInvLineNumbers.contains(line);
  }

  private void exportPlainInvariantForLine(int line, String invariant) throws IOException {

    StringBuilder sb = new StringBuilder("[");
    sb.append(line);

    //append token for relative positioning of invariant
    String token = invariantPosMap.get(line);
    if (token == null) {
      token = ""; //just add emptry string
    }
    sb.append(token);

    sb.append(",");
    sb.append(invariant.replaceAll("\n", " "));
    sb.append("]\n");

    IO.appendToFile(prefix.getPath("plain.txt"), Charset.defaultCharset(), sb.toString());
  }
}
