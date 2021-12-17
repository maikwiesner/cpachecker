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
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
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

  private final PathTemplate prefix;

  private final FormulaManagerView fmgr;
  private final BooleanFormulaManager bfmgr;
  private final FormulaToCExpressionConverter formulaToCExpressionConverter;
  private final InductiveWeakeningManager inductiveWeakeningManager;

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
   * creates output file for exported invariants and initializes @see{plainInvLineNumbers}
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
          try {
            plainInvLineNumbers.add(Integer.parseInt(lineNumber));
          } catch (NumberFormatException e) {
            //print warning and ignore this value
            pLogManager.log(Level.WARNING,
                "could not parse line number " + lineNumber + ", skipping!");
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

        //look for main function header
        //TODO: find better implementation for this. What if there is no main function?
        if (line.contains("main(")) {
          out.append("extern void __VERIFIER_assume(int expression);\n");
          out.append("//void __VERIFIER_assume(int expression) { if (!expression) { LOOP: goto LOOP; }; return; }\n\n");
        }

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
            byState.put(location.getStartingLineInOrigin(), reported);
          }
        }
      }
    }
    return Maps.transformValues(
        byState.asMap(), invariants -> bfmgr.or(invariants)
    );
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
    sb.append(",");
    sb.append(invariant.replaceAll("\n", " "));
    sb.append("]\n");

    IO.appendToFile(prefix.getPath("plain.txt"), Charset.defaultCharset(), sb.toString());
  }
}
