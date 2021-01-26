// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.core.algorithm.residualprogram;

import static java.util.stream.Collectors.partitioningBy;

import com.google.common.collect.ImmutableSet;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.algorithm.NestingAlgorithm;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.reachedset.AggregatedReachedSets;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.specification.Specification;
import org.sosy_lab.cpachecker.core.waitlist.Waitlist.TraversalMethod;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.stopatleaves.StopAtLeavesCPA;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.CPAs;

/**
 * Algorithm to convert a list of covered test goal labels to a condition.
 */
@Options(prefix="conditional_testing")
public class TestGoalToConditionConverterAlgorithm extends NestingAlgorithm {
        /**
         * States a goal can be in.
         */
        enum LeafStates {
                COVERED(true),
                UNCOVERED(false);

                LeafStates(boolean b) {
                        isCovered = b;
                }

                private final boolean isCovered;

                public boolean isCovered() {
                        return isCovered;
                }
        }

        /**
         * A list of the strategy to use. Is used by our configuration.
         * Note: Actually this is bad style. We should rather use reflection. If someone were
         * to implement a new strategy they also would have to modify this enum which shouldn't be necessary.
         */
        public enum Strategy {
                NAIVE, PROPAGATION
        }

        private Algorithm backwardsCpaAlgorithm;
        private ConfigurableProgramAnalysis backwardsCpa;

        private final Algorithm outerAlgorithm;
        private final ConfigurableProgramAnalysis outerCpa;

        @Option(
          secure = true,
          name = "inputfile",
          description = "The input file with all goals that were previously reached")
        @FileOption(FileOption.Type.REQUIRED_INPUT_FILE)
        private Path inputfile;

        @Option(
          secure = true,
          name = "strategy",
          description = "The strategy to use"
        )
        Strategy strategy;

        private final IGoalFindingStrategy goalFindingStrategy;

        public TestGoalToConditionConverterAlgorithm(Configuration pConfig, LogManager pLogger, ShutdownNotifier pShutdownNotifier,
                Specification pSpecification, CFA pCfa, Algorithm pOuter, ConfigurableProgramAnalysis pOuterCpa) throws InvalidConfigurationException {

                super(pConfig, pLogger, pShutdownNotifier, Specification.alwaysSatisfied(), pCfa);
                pConfig.inject(this);

                switch (strategy) {
                        case NAIVE:
                                goalFindingStrategy = new LeafGoalStrategy();
                                break;
                        case PROPAGATION:
                                goalFindingStrategy = new LeafGoalWithPropagationStrategy();
                                break;
                        default:
                                throw new InvalidConfigurationException("A strategy must be selected!");
                }
                try {
                        var backwardsCpaTriple = this.createAlgorithm(
                          Path.of("config/components/goalConverterBackwardsSearch.properties"),
                          pCfa.getMainFunction(),
                          ShutdownManager.createWithParent(pShutdownNotifier),
                          new AggregatedReachedSets(),
                          List.of(
                                "analysis.testGoalConverter",
                                "cpa",
                                "specification",
                                "ARGCPA.cpa",
                                "cpa.property_reachability.noFollowBackwardsUnreachable",
                                "analysis.initialStatesFor",
                                "CompositeCPA.cpas",
                                "cpa.callstack.traverseBackwards",
                                "analysis.collectAssumptions",
                                "assumptions.automatonFile"
                          ),
                          new HashSet<>()
                        );

                        backwardsCpaAlgorithm = backwardsCpaTriple.getFirst();
                        backwardsCpa = backwardsCpaTriple.getSecond();
                } catch (Exception e) {
                        backwardsCpaAlgorithm = null;
                        backwardsCpa = null;
                }

                if(pOuter == null || pOuterCpa == null) {
                        throw new InvalidConfigurationException("A valid pOuter algorithm must be specified!");
                }

                outerAlgorithm = pOuter;
                outerCpa = pOuterCpa;
        }

        @Override public AlgorithmStatus run(ReachedSet reachedSet)
          throws CPAException, InterruptedException {
                try {
                        var leafGoals = getPartitionedLeafGoals();

                        var stopAtLeavesCpa = CPAs.retrieveCPAOrFail(outerCpa, StopAtLeavesCPA.class, StopAtLeavesCPA.class);
                        stopAtLeavesCpa.setLeaves(leafGoals.get(LeafStates.UNCOVERED));
                        var result = outerAlgorithm.run(reachedSet);


                        return result;
                } catch(Exception e) {
                        throw new CPAException(e.getLocalizedMessage());
                }
        }

        /**
         * Reads the input file and extracts all covered goals.
         * @return A list of all covered goals.
         * @throws CPAException when file could not be read or another IO error occurs.
         */
        private Set<String> getCoveredGoals() throws CPAException {

                try (var lines = Files.lines(inputfile)) {
                        return lines.collect(Collectors.toSet());
                } catch(IOException e) {
                        throw new CPAException(e.getLocalizedMessage());
                }
        }

        /**
         * Gets all leaf goals in the program. They are partitioned into LeafStates.COVERED and LeaftStates.UNCOVERED.
         * @return A map with two keys (COVERED, UNCOVERED) of all leaf goals
         * @throws CPAException Thrown when there is an error in the cpa algorithm
         */
        private Map<LeafStates, List<CFANode>> getPartitionedLeafGoals()
          throws CPAException, InterruptedException {

                var reachedSet = buildBackwardsReachedSet();
                var coveredGoals = getCoveredGoals();

                backwardsCpaAlgorithm.run(reachedSet);

                ArrayList<ARGState> waitList = new ArrayList<>();
                //We're doing a backwards analysis; hence the first state here is the end of the ARG
                waitList.add((ARGState) reachedSet.getFirstState());

                var result = goalFindingStrategy.findGoals(waitList, coveredGoals);

                return result;
        }

        /**
         * This function builds a reached set that has PROGRAM_SINKS as initial states.
         * We need to build it by hand since the option <pre>analysis.initialStatesFor = PROGRAM_SINKS</pre>
         * is only read once when constructing @see{CPAchecker}.
         * @return A reached set that has the PROGRAM_SINKS as initial states
         */
        @Nonnull
        private ReachedSet buildBackwardsReachedSet() throws InterruptedException {
                var reachedSet = new PartitionedReachedSet(TraversalMethod.DFS);
                var initialLocations =
                  ImmutableSet.<CFANode>builder()
                        .addAll(
                          CFAUtils.getProgramSinks(
                                cfa, cfa.getLoopStructure().orElseThrow(), cfa.getMainFunction()))
                        .build();

                for (var loc: initialLocations) {
                        var partition = StateSpacePartition.getDefaultPartition();
                        var state = backwardsCpa.getInitialState(loc, partition);
                        var precision = backwardsCpa.getInitialPrecision(loc, partition);
                        reachedSet.add(state, precision);
                }

                return reachedSet;
        }

        @Override public void collectStatistics(Collection<Statistics> statsCollection) {

        }
}
