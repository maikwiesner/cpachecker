/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cpa.value.symbolic;

import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Function;
import java.io.PrintStream;
import java.util.Optional;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustmentResult;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisCPAStatistics;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisPrecisionAdjustment;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisPrecisionAdjustment.PrecAdjustmentOptions;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisPrecisionAdjustment.PrecAdjustmentStatistics;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.cpa.value.symbolic.type.SymbolicValue;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.statistics.StatInt;
import org.sosy_lab.cpachecker.util.statistics.StatKind;
import org.sosy_lab.cpachecker.util.statistics.StatisticsWriter;

/**
 * Precision adjustment for the {@link org.sosy_lab.cpachecker.cpa.value.symbolic symbolic} {@link
 * org.sosy_lab.cpachecker.cpa.value.ValueAnalysisCPA}. It has the same semantics as {@link
 * org.sosy_lab.cpachecker.cpa.value.ValueAnalysisPrecisionAdjustment
 * ValueAnalysisPrecisionAdjustment}, but collects additional statistics for symbolic values.
 */
public class SymbolicValueAnalysisPrecisionAdjustment implements PrecisionAdjustment {

  private final PrecisionAdjustment delegate;
  private final SymbolicStatistics symbolicStats;

  public SymbolicValueAnalysisPrecisionAdjustment(
      final ValueAnalysisCPAStatistics pStats,
      final CFA pCfa,
      final PrecAdjustmentOptions pOptions,
      final PrecAdjustmentStatistics pStatistics,
      final SymbolicStatistics pSymbolicStats) {
    delegate = new ValueAnalysisPrecisionAdjustment(pStats, pCfa, pOptions, pStatistics);
    symbolicStats = pSymbolicStats;
  }

  @Override
  public Optional<PrecisionAdjustmentResult> prec(
      AbstractState pState,
      Precision pPrecision,
      UnmodifiableReachedSet pStates,
      Function<AbstractState, AbstractState> pStateProjection,
      AbstractState pFullState)
      throws CPAException, InterruptedException {

    checkState(
        pState instanceof ValueAnalysisState,
        "State not instance of ValueAnalysisState, but %s",
        pState.getClass().getSimpleName());

    ValueAnalysisState valState = (ValueAnalysisState) pState;

    symbolicStats.symbolicValuesBefore.setNextValue(getSymbolicValueCount(valState));

    Optional<PrecisionAdjustmentResult> maybeAdjusted =
        delegate.prec(pState, pPrecision, pStates, pStateProjection, pFullState);

    if (maybeAdjusted.isPresent()) {
      ValueAnalysisState newValState = (ValueAnalysisState) maybeAdjusted.get().abstractState();
      symbolicStats.symbolicValuesAfter.setNextValue(getSymbolicValueCount(newValState));
    }
    return maybeAdjusted;
  }

  private int getSymbolicValueCount(ValueAnalysisState pState) {
    // it's safe to cast to int here because we will never have that many program variables
    return (int)
        pState
            .getConstants()
            .stream()
            .filter(e -> e.getValue().getValue() instanceof SymbolicValue)
            .count();
  }

  public static class SymbolicStatistics implements Statistics {
    private final StatInt symbolicValuesBefore =
        new StatInt(StatKind.SUM, "Symbolic values before refinement");
    private final StatInt symbolicValuesAfter =
        new StatInt(StatKind.SUM, "Symbolic values after refinement");

    @Override
    public void printStatistics(PrintStream pOut, Result pResult, UnmodifiableReachedSet pReached) {
      StatisticsWriter.writingStatisticsTo(pOut).put(symbolicValuesBefore).put(symbolicValuesAfter);
    }

    @Override
    public String getName() {
      return SymbolicValueAnalysisPrecisionAdjustment.class.getSimpleName();
    }
  }
}
