// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.automatic_program_repair;

import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;

public class SimpleMutation extends Mutation {
  private CFAEdge newEdge;

  public SimpleMutation(CFAEdge pSuspiciousEdge, CFAEdge pNewEdge, CFA pCFA) {
    super(pSuspiciousEdge, pCFA);
    newEdge = pNewEdge;

    exchangeEdge(newEdge);
  }

  public CFAEdge getNewEdge() {
    return newEdge;
  }
}
