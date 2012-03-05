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
package org.sosy_lab.cpachecker.cpa.impact;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.cpachecker.cfa.objectmodel.CFANode;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.SingletonPrecision;
import org.sosy_lab.cpachecker.core.defaults.StaticPrecisionAdjustment;
import org.sosy_lab.cpachecker.core.defaults.StopSepOperator;
import org.sosy_lab.cpachecker.core.interfaces.AbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractElement;
import org.sosy_lab.cpachecker.core.interfaces.CPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.cpa.predicate.blocking.DefaultBlockOperator;
import org.sosy_lab.cpachecker.util.predicates.CachingPathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.ExtendedFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.FormulaManagerFactory;
import org.sosy_lab.cpachecker.util.predicates.PathFormulaManagerImpl;
import org.sosy_lab.cpachecker.util.predicates.Solver;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.TheoremProver;

public class ImpactCPA implements ConfigurableProgramAnalysis {

  public static CPAFactory factory() {
    return AutomaticCPAFactory.forType(ImpactCPA.class).withOptions(DefaultBlockOperator.class);
  }

  private final Configuration config;
  private final LogManager logger;

  private final ExtendedFormulaManager fmgr;
  private final PathFormulaManager pfmgr;
  private final Solver solver;
  private final FormulaManagerFactory factory;

  private final AbstractDomain abstractDomain;
  private final MergeOperator mergeOperator;
  private final StopOperator stopOperator;
  private final TransferRelation transferRelation;

  private ImpactCPA(Configuration pConfig, LogManager pLogger, DefaultBlockOperator blk) throws InvalidConfigurationException {
    config = pConfig;
    logger = pLogger;

    factory = new FormulaManagerFactory(pConfig, pLogger);
    fmgr = new ExtendedFormulaManager(factory.getFormulaManager(), pConfig, pLogger);

    pfmgr = new CachingPathFormulaManager(new PathFormulaManagerImpl(fmgr, config, logger));
    TheoremProver prover = factory.createTheoremProver();
    solver = new Solver(fmgr, prover);

    abstractDomain = new ImpactAbstractDomain(solver);
    mergeOperator = new ImpactMergeOperator(logger, pfmgr);
    stopOperator = new StopSepOperator(abstractDomain);
    transferRelation = new ImpactTransferRelation(logger, blk, fmgr, pfmgr, solver);
  }

  public LogManager getLogManager() {
    return logger;
  }

  public Configuration getConfiguration() {
    return config;
  }

  public ExtendedFormulaManager getFormulaManager() {
    return fmgr;
  }

  public PathFormulaManager getPathFormulaManager() {
    return pfmgr;
  }

  public Solver getSolver() {
    return solver;
  }

  FormulaManagerFactory getFormulaManagerFactory() {
    return factory;
  }

  @Override
  public AbstractDomain getAbstractDomain() {
    return abstractDomain;
  }

  @Override
  public TransferRelation getTransferRelation() {
    return transferRelation;
  }

  @Override
  public MergeOperator getMergeOperator() {
    return mergeOperator;
  }

  @Override
  public StopOperator getStopOperator() {
    return stopOperator;
  }

  @Override
  public PrecisionAdjustment getPrecisionAdjustment() {
    return StaticPrecisionAdjustment.getInstance();
  }

  @Override
  public AbstractElement getInitialElement(CFANode pNode) {
    return new ImpactAbstractElement.AbstractionElement(pfmgr.makeEmptyPathFormula(), fmgr.makeTrue(), pfmgr.makeEmptyPathFormula());
  }

  @Override
  public Precision getInitialPrecision(CFANode pNode) {
    return SingletonPrecision.getInstance();
  }
}