/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2012  Dirk Beyer
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
package org.sosy_lab.cpachecker.cpa.fsmbdd;

import org.sosy_lab.cpachecker.core.interfaces.AbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.exceptions.CPAException;

/**
 * Merge-Operator of the FsmBddCPA.
 * Merge is done by joining the abstract states;
 * this is done by constructing the disjunction (OR) of their BDDs.
 */
public class FsmMergeOperator implements MergeOperator {

  private final AbstractDomain domain;
  private final FsmBddStatistics statistics;

  public FsmMergeOperator(AbstractDomain pDomain, FsmBddStatistics pStatistics)
  {
    this.domain = pDomain;
    this.statistics = pStatistics;
  }

  @Override
  public AbstractState merge(AbstractState pState1, AbstractState pState2, Precision pPrecision) throws CPAException {
    FsmState state1 = (FsmState) pState1;
    FsmState state2 = (FsmState) pState2;

//    System.out.printf("M %d <> %d ?\n", state1.getCfaNode().getNodeNumber(), state2.getCfaNode().getNodeNumber());
//    System.out.println(state1);
//    System.out.println(state2);

    if (state1.getStateBdd().equals(state2.getStateBdd())) {
      FsmState result = state1.cloneState(state1.getCfaNode());
      result.addToConditionBlock(state2.getConditionBlock(), false);
      statistics.mergesBecauseEqualBdd++;
      return result;
    } else if (state1.condBlockEqualToBlockOf(state2)) {
        if (state1.getConditionBlock() == null) {
          statistics.mergesBecauseBothEmptySyntax++;
        } else {
          statistics.mergesBecauseEqualSyntax++;
        }
        state1.addDebugInfo("merged", "equalSyntax");
        state2.addDebugInfo("merged", "equalSyntax");
        return domain.join(state1, state2);
    } else {
      return state2;
    }
  }


}
