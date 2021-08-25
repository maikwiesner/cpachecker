// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.concurrent.task.forward;

import static org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition.getDefaultPartition;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.blockgraph.Block;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm.AlgorithmStatus;
import org.sosy_lab.cpachecker.core.algorithm.concurrent.ShareableBooleanFormula;
import org.sosy_lab.cpachecker.core.algorithm.concurrent.task.Task;
import org.sosy_lab.cpachecker.core.algorithm.concurrent.task.TaskManager;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.composite.BlockAwareCompositeCPA;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPA;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.smt.FormulaManagerView;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;

public class ForwardAnalysis implements Task {
  private final Block target;
  private final int expectedVersion;
  private final ShareableBooleanFormula newSummary;
  private final ShareableBooleanFormula oldSummary;
  private final ReachedSet reached;
  private final TaskManager taskManager;
  private final LogManager logManager;
  private final ShutdownNotifier shutdownNotifier;
  private final FormulaManagerView formulaManager;
  private final BooleanFormulaManager bfMgr;
  private final ImmutableList<ShareableBooleanFormula> predecessorSummaries;
  private final Algorithm algorithm;
  private final BlockAwareCompositeCPA cpa;

  public ForwardAnalysis(
      final Block pTarget,
      @Nullable final ShareableBooleanFormula pOldSummary,
      @Nullable final ShareableBooleanFormula pNewSummary,
      final int pExpectedVersion,
      final ReachedSet pReachedSet,
      final TaskManager pTaskManager,
      final LogManager pLogManager,
      final ShutdownNotifier pShutdownNotifier,
      final FormulaManagerView pFormulaManager,
      final ImmutableList<ShareableBooleanFormula> pPredecessorSummaries,
      final Algorithm pAlgorithm,
      final BlockAwareCompositeCPA pCPA) {
    target = pTarget;
    oldSummary = pOldSummary;
    newSummary = pNewSummary;
    expectedVersion = pExpectedVersion;
    reached = pReachedSet;
    taskManager = pTaskManager;
    logManager = pLogManager;
    shutdownNotifier = pShutdownNotifier;
    formulaManager = pFormulaManager;
    bfMgr = formulaManager.getBooleanFormulaManager();
    predecessorSummaries = pPredecessorSummaries;
    algorithm = pAlgorithm;
    cpa = pCPA;
  }

  @Override
  public AlgorithmStatus call()
      throws CPAException, InterruptedException, InvalidConfigurationException {
    if (!summaryHasChanged()) {
      return AlgorithmStatus.NO_PROPERTY_CHECKED;
    }

    Precision precision = cpa.getInitialPrecision(target.getEntry(), getDefaultPartition());
    AbstractState rawInitialState = null;
    while (rawInitialState == null) {
      try {
        rawInitialState = cpa.getInitialState(target.getEntry(), getDefaultPartition());
      } catch (InterruptedException ignored) {
        shutdownNotifier.shutdownIfNecessary();
      }
    }

    PredicateAbstractState rawPredicateState =
        AbstractStates.extractStateByType(rawInitialState, PredicateAbstractState.class);
    assert rawPredicateState != null;

    BooleanFormula cumPredSummary;
    if (predecessorSummaries.isEmpty()) {
      cumPredSummary = bfMgr.makeTrue();
    } else {
      List<BooleanFormula> summaries =
          predecessorSummaries.stream()
              .map(summary -> summary.getFor(formulaManager))
              .collect(Collectors.toList());

      cumPredSummary = bfMgr.or(summaries);
    }

    if (oldSummary != null) {
      BooleanFormula addedContext =
          bfMgr.and(
              oldSummary.getFor(formulaManager), bfMgr.not(newSummary.getFor(formulaManager)));
      BooleanFormula relevantChange = bfMgr.implication(cumPredSummary, addedContext);
      if (bfMgr.isFalse(relevantChange)) {
        return AlgorithmStatus.NO_PROPERTY_CHECKED;
      }
    }

    BooleanFormula newContext = bfMgr.or(cumPredSummary, newSummary.getFor(formulaManager));
    PathFormula context = rawPredicateState.getPathFormula().withFormula(newContext);

    PredicateAbstractState predicateState =
        PredicateAbstractState.mkNonAbstractionStateWithNewPathFormula(context, rawPredicateState);

    List<AbstractState> componentStates = new ArrayList<>();
    for (ConfigurableProgramAnalysis componentCPA : cpa.getWrappedCPAs()) {
      AbstractState componentState = null;
      if (componentCPA instanceof PredicateCPA) {
        componentState = predicateState;
      } else {
        while (componentState == null) {
          try {
            componentState = componentCPA.getInitialState(target.getEntry(), getDefaultPartition());
          } catch (InterruptedException ignored) {
            shutdownNotifier.shutdownIfNecessary();
          }
        }
      }
      componentStates.add(componentState);
    }

    AbstractState entryState = new CompositeState(componentStates);
    reached.add(entryState, precision);

    logManager.log(Level.FINE, "Starting ForwardAnalysis on ", target);
    AlgorithmStatus status = algorithm.run(reached);

    for (final AbstractState state : reached.asCollection()) {
      if (AbstractStates.isTargetState(state)) {
        logManager.log(Level.FINE, "Target State:", state);
      }

      LocationState location = AbstractStates.extractStateByType(state, LocationState.class);
      assert location != null;

      if (target.getExits().containsKey(location.getLocationNode())) {
        PredicateAbstractState predState =
            AbstractStates.extractStateByType(state, PredicateAbstractState.class);
        assert predState != null;

        BooleanFormula exitFormula = predState.getPathFormula().getFormula();

        Block exit = target.getExits().get(location.getLocationNode());
        final ShareableBooleanFormula shareableFormula =
            new ShareableBooleanFormula(formulaManager, exitFormula);

        taskManager.spawnForwardAnalysis(target, expectedVersion, exit, shareableFormula);
      }
    }

    logManager.log(Level.FINE, "Completed ForwardAnalysis on ", target);
    return status.update(AlgorithmStatus.NO_PROPERTY_CHECKED);
  }

  private boolean summaryHasChanged() {
    if (oldSummary == null || newSummary == null) {
      return true;
    }

    BooleanFormula newFormula = newSummary.getFor(formulaManager);
    BooleanFormula oldFormula = oldSummary.getFor(formulaManager);
    BooleanFormula equivalence = bfMgr.equivalence(newFormula, oldFormula);

    return bfMgr.isFalse(equivalence);
  }
}
