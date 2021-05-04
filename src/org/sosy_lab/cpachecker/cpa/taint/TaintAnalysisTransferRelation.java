// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.taint;

import java.util.List;
import java.util.logging.Level;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.AArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.AAssignment;
import org.sosy_lab.cpachecker.cfa.ast.ABinaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.ADeclaration;
import org.sosy_lab.cpachecker.cfa.ast.AExpression;
import org.sosy_lab.cpachecker.cfa.ast.AExpressionStatement;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.AFunctionCallStatement;
import org.sosy_lab.cpachecker.cfa.ast.AIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.AInitializer;
import org.sosy_lab.cpachecker.cfa.ast.AInitializerExpression;
import org.sosy_lab.cpachecker.cfa.ast.ALiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.AParameterDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.APointerExpression;
import org.sosy_lab.cpachecker.cfa.ast.ARightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.AStatement;
import org.sosy_lab.cpachecker.cfa.ast.AUnaryExpression;
import org.sosy_lab.cpachecker.cfa.ast.AVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CBinaryExpression.BinaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CUnaryExpression.UnaryOperator;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFieldReference;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCall;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallAssignmentStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFunctionCallStatement;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CLeftHandSide;
import org.sosy_lab.cpachecker.cfa.ast.java.JArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.java.JFieldDeclaration;
import org.sosy_lab.cpachecker.cfa.model.ADeclarationEdge;
import org.sosy_lab.cpachecker.cfa.model.AReturnStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.AStatementEdge;
import org.sosy_lab.cpachecker.cfa.model.AssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.BlankEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionCallEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionReturnEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.types.Type;
import org.sosy_lab.cpachecker.core.defaults.ForwardingTransferRelation;
import org.sosy_lab.cpachecker.core.defaults.precision.VariableTrackingPrecision;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.exceptions.UnsupportedCodeException;
import org.sosy_lab.cpachecker.util.BuiltinOverflowFunctions;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

public class TaintAnalysisTransferRelation
    extends ForwardingTransferRelation<
        TaintAnalysisState, TaintAnalysisState, VariableTrackingPrecision> {

  @Options(prefix = "cpa.taint")
  public static class TaintTransferOptions {

    @Option(
        secure = true,
        name = "useCriticalSourceFunctions",
        description =
            "Determines if predefined critical functions should be used as taint sources.")
    private boolean useCriticalSourceFunctions = true;

    @Option(
        secure = true,
        name = "useCriticalSinkFunctions",
        description = "Determines if predefined critical functions should be used as taint sinks.")
    private boolean useCriticalSinkFunctions = true;

    public TaintTransferOptions(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }

    boolean isUseCriticalSourceFunctions() {
      return useCriticalSourceFunctions;
    }

    boolean isUseCriticalSinkFunctions() {
      return useCriticalSinkFunctions;
    }
  }

  private final TaintTransferOptions options;
  private final LogManagerWithoutDuplicates logger;

  public TaintAnalysisTransferRelation(LogManager pLogger, TaintTransferOptions pOptions) {
    logger = new LogManagerWithoutDuplicates(pLogger);
    options = pOptions;
    // stats = pStats;

    // if (pCfa.getVarClassification().isPresent()) {
    // addressedVariables = pCfa.getVarClassification().orElseThrow().getAddressedVariables();
    // booleanVariables = pCfa.getVarClassification().orElseThrow().getIntBoolVars();
    // } else {
    // addressedVariables = ImmutableSet.of();
    // booleanVariables = ImmutableSet.of();
    // }

    // unknownValueHandler = pUnknownValueHandler;
    // constraintsStrengthenOperator = pConstraintsStrengthenOperator;
  }

  // @Override
  // protected Collection<TaintAnalysisState> postProcessing(TaintAnalysisState successor, CFAEdge
  // edge) {
  // // always return a new state (requirement for strengthening states with interpolants)
  // if (successor != null) {
  // successor = TaintAnalysisState.copyOf(successor);
  // }

  // return super.postProcessing(successor, edge);
  // }

  @Override
  protected void setInfo(
      AbstractState pAbstractState, Precision pAbstractPrecision, CFAEdge pCfaEdge) {
    super.setInfo(pAbstractState, pAbstractPrecision, pCfaEdge);
  }

  @Override
  protected TaintAnalysisState handleFunctionCallEdge(
      FunctionCallEdge callEdge,
      List<? extends AExpression> arguments,
      List<? extends AParameterDeclaration> parameters,
      String calledFunctionName)
      throws UnrecognizedCodeException {
    TaintAnalysisState newElement = TaintAnalysisState.copyOf(state);

    assert (parameters.size() == arguments.size())
        || callEdge.getSuccessor().getFunctionDefinition().getType().takesVarArgs();

    // visitor for getting the values of the actual parameters in caller function context
    // final ExpressionValueVisitor visitor = getVisitor();

    // get value of actual parameter in caller function context
    for (int i = 0; i < parameters.size(); i++) {
      AExpression exp = arguments.get(i);
      logger.log(Level.INFO, "YAS" + exp);

      // if (exp instanceof JExpression) {
      // value = ((JExpression) exp).accept(visitor);
      // } else if (exp instanceof CExpression) {
      // value = visitor.evaluate((CExpression) exp, (CType) parameters.get(i).getType());
      // } else {
      // throw new AssertionError("Unknown expression: " + exp);
      // }

      // AParameterDeclaration param = parameters.get(i);
      // String paramName = param.getName();
      // Type paramType = param.getType();

      // MemoryLocation formalParamName = MemoryLocation.valueOf(calledFunctionName, paramName);

      // if (value.isUnknown()) {
      // if (isMissingCExpressionInformation(visitor, exp)) {
      // addMissingInformation(formalParamName, exp);
      // }

      // unknownValueHandler.handle(formalParamName, paramType, newElement, visitor);

      // } else {
      // newElement.assignConstant(formalParamName, value, paramType);
      // }

      // visitor.reset();

    }

    return newElement;
  }

  @Override
  protected TaintAnalysisState handleBlankEdge(BlankEdge cfaEdge) {
    if (cfaEdge.getSuccessor() instanceof FunctionExitNode) {
      // clone state, because will be changed through removing all variables of current function's
      // scope
      state = TaintAnalysisState.copyOf(state);
      // state.dropFrame(functionName);
    }

    return state;
  }

  @Override
  protected TaintAnalysisState handleReturnStatementEdge(AReturnStatementEdge returnEdge)
      throws UnrecognizedCodeException {

    // visitor must use the initial (previous) state, because there we have all information about
    // variables
    // ExpressionValueVisitor evv = getVisitor();

    // clone state, because will be changed through removing all variables of current function's
    // scope.
    // The assignment of the global 'state' is safe, because the 'old state'
    // is available in the visitor and is not used for further computation.
    state = TaintAnalysisState.copyOf(state);
    // logger.log(Level.INFO, "");
    // state.dropFrame(functionName);

    // AExpression expression = returnEdge.getExpression().orNull();
    // if (expression == null && returnEdge instanceof CReturnStatementEdge) {
    // expression = CIntegerLiteralExpression.ZERO; // this is the default in C
    // }

    // final FunctionEntryNode functionEntryNode = returnEdge.getSuccessor().getEntryNode();

    // final com.google.common.base.Optional<? extends AVariableDeclaration>
    // optionalReturnVarDeclaration = functionEntryNode.getReturnVariable();
    // MemoryLocation functionReturnVar = null;

    // if (optionalReturnVarDeclaration.isPresent()) {
    // functionReturnVar =
    // MemoryLocation.valueOf(optionalReturnVarDeclaration.get().getQualifiedName());
    // }

    // if (expression != null && functionReturnVar != null) {
    // final Type functionReturnType =
    // functionEntryNode.getFunctionDefinition().getType().getReturnType();

    // return handleAssignmentToVariable(functionReturnVar,
    // functionReturnType,
    // expression,
    // evv);
    // } else {
    // return state;
    // }
    return state;
  }

  /**
   * Handles return from one function to another function.
   *
   * @param functionReturnEdge return edge from a function to its call site
   * @return new abstract state
   */
  @Override
  protected TaintAnalysisState handleFunctionReturnEdge(
      FunctionReturnEdge functionReturnEdge,
      FunctionSummaryEdge summaryEdge,
      AFunctionCall exprOnSummary,
      String callerFunctionName)
      throws UnrecognizedCodeException {

    TaintAnalysisState newElement = TaintAnalysisState.copyOf(state);

    return newElement;
  }

  @Override
  protected TaintAnalysisState handleFunctionSummaryEdge(CFunctionSummaryEdge cfaEdge)
      throws CPATransferException {
    TaintAnalysisState newState = TaintAnalysisState.copyOf(state);
    // AFunctionCall functionCall = cfaEdge.getExpression();

    // if (functionCall instanceof AFunctionCallAssignmentStatement) {
    // AFunctionCallAssignmentStatement assignment =
    // ((AFunctionCallAssignmentStatement)functionCall);
    // AExpression leftHandSide = assignment.getLeftHandSide();

    // if (leftHandSide instanceof CLeftHandSide) {
    // MemoryLocation assignedMemoryLocation = getVisitor().evaluateMemoryLocation((CLeftHandSide)
    // leftHandSide);

    // if (newState.contains(assignedMemoryLocation)) {
    // newState.forget(assignedMemoryLocation);
    // }
    // }
    // }

    return newState;
  }

  @Override
  protected TaintAnalysisState handleAssumption(
      AssumeEdge cfaEdge, AExpression expression, boolean truthValue)
      throws UnrecognizedCodeException {
    return state;
  }
  // private Type getBooleanType(AExpression pExpression) {
  // if (pExpression instanceof JExpression) {
  // return JSimpleType.getBoolean();
  // } else if (pExpression instanceof CExpression) {
  // return CNumericTypes.INT;

  // } else {
  // throw new AssertionError("Unhandled expression type " + pExpression.getClass());
  // }
  // }

  /*
   * returns 'true' if the given value represents the specified boolean bool. A return of 'false'
   * does not necessarily mean that the given value represents !bool, but only that it does not
   * represent bool.
   *
   * For example: * representsTrue(BooleanValue.valueOf(true), true) = true *
   * representsTrue(BooleanValue.valueOf(false), true) = false but: *
   * representsTrue(NullValue.getInstance(), true) = false * representsTrue(NullValue.getInstance(),
   * false) = false
   *
   */
  // private boolean representsBoolean(Value value, boolean bool) {
  // if (value instanceof BooleanValue) {
  // return ((BooleanValue) value).isTrue() == bool;

  // } else if (value.isNumericValue()) {
  // return value.equals(new NumericValue(bool ? 1L : 0L));

  // } else {
  // return false;
  // }
  // }

  @Override
  protected TaintAnalysisState handleDeclarationEdge(
      ADeclarationEdge declarationEdge, ADeclaration declaration) throws UnrecognizedCodeException {
    
    if (!(declaration instanceof AVariableDeclaration)) {
      return state;
    }
    
    TaintAnalysisState newElement = TaintAnalysisState.copyOf(state);
    AVariableDeclaration decl = (AVariableDeclaration) declaration;
    Type declarationType = decl.getType();

    // get the variable name in the declarator
    String varName = decl.getName();

    // Value initialValue = getDefaultInitialValue(decl);

    // // get initializing statement
    AInitializer init = decl.getInitializer();

    MemoryLocation memoryLocation;

    // assign initial value if necessary
    if (decl.isGlobal()) {
      memoryLocation = MemoryLocation.valueOf(varName);
    } else {
      memoryLocation = MemoryLocation.valueOf(functionName, varName);
    }

    newElement.assignTaint(memoryLocation, false);
    String msg;
    msg = memoryLocation + " | tainted: false | Type: " + declarationType;

    if (init instanceof AInitializerExpression) {
      AExpression exp = ((AInitializerExpression) init).getExpression();
      if(exp instanceof AUnaryExpression) {
        AUnaryExpression unary = (AUnaryExpression) exp;
        if(unary.getOperator() == UnaryOperator.AMPER) {
          MemoryLocation dest = MemoryLocation.valueOf(functionName, unary.getOperand().toString());
          newElement.addPointerTo(memoryLocation, dest);
          msg = msg + " | Pointer " + memoryLocation + " points to " + dest;
        }
      }
      else if(exp instanceof APointerExpression) {
        APointerExpression pointer = (APointerExpression) exp;
        MemoryLocation p = MemoryLocation.valueOf(functionName, pointer.getOperand().toString());
        MemoryLocation dest = newElement.getPointerTo(p);
        logger.log(Level.INFO, msg);
        newElement.change(memoryLocation, newElement.getStatus(dest));
        msg = msg + " | data from pointer: " + dest +" => tainted: "+newElement.getStatus(dest);
      }
      msg = msg + " | EXP: " + exp;
    }
    logger.log(Level.INFO, msg);
    return newElement;
  }

  @Override
  protected TaintAnalysisState handleStatementEdge(AStatementEdge cfaEdge, AStatement expression)
      throws UnrecognizedCodeException {

    TaintAnalysisState newElement = TaintAnalysisState.copyOf(state);

    String msg = "";

    if (expression instanceof CFunctionCall) {
      CFunctionCall functionCall = (CFunctionCall) expression;
      CFunctionCallExpression functionCallExp = functionCall.getFunctionCallExpression();
      CExpression fn = functionCallExp.getFunctionNameExpression();

      msg =
          msg
              + "functionCall: "
              + functionCall
              + " | functionCallExp: "
              + functionCallExp
              + " | fn: "
              + fn;

      if (fn instanceof CIdExpression) {
        String func = ((CIdExpression) fn).getName();
        msg = msg + " | func: " + func;
        if (expression instanceof CFunctionCallAssignmentStatement) {
          msg = msg + " | CFunctionCallAssignmentStatement";
          CFunctionCallAssignmentStatement pFunctionCallAssignment =
              (CFunctionCallAssignmentStatement) expression;
          final CLeftHandSide leftSide = pFunctionCallAssignment.getLeftHandSide();
          msg = msg + " | leftSide: " + leftSide;
          if (options.isUseCriticalSourceFunctions()) {
            msg = msg + " | useCriticalSourceFunctions: True";
            if (func.equals("getchar")
                || func.equals("scanf")
                || func.equals("gets")
                || func.equals("fopen")) {
              MemoryLocation memoryLocation = MemoryLocation.valueOf(functionName, leftSide.toString());
              newElement.change(memoryLocation, true);
            }
          } else msg = msg + " | useCriticalSourceFunctions: False";
        } else if (BuiltinOverflowFunctions.isBuiltinOverflowFunction(func)) {
          if (!BuiltinOverflowFunctions.isFunctionWithoutSideEffect(func)) {
            throw new UnsupportedCodeException(func + " is unsupported for this analysis", null);
          }
        } else if (expression instanceof CFunctionCallAssignmentStatement) {
          msg = msg + " | CFunctionCallAssignmentStatement";
        } else if (expression instanceof CFunctionCallStatement) {
          msg = msg + " | CFunctionCallStatement";
          AFunctionCallStatement stm = (AFunctionCallStatement) expression;
          AFunctionCallExpression exp = stm.getFunctionCallExpression();
          AExpression param = exp.getParameterExpressions().get(0);
          // VERIFIER logic
          MemoryLocation memoryLocation = MemoryLocation.valueOf(functionName, param.toString());
          if (func.equals("__VERIFIER_mark_tainted")) {
            newElement.change(memoryLocation, true);
          } else if (func.equals("__VERIFIER_mark_untainted")) {
            newElement.change(memoryLocation, false);
          } else if (func.equals("__VERIFIER_assert_untainted")) {
            if (state.getStatus(memoryLocation)) {
              newElement =
                  TaintAnalysisState.copyOf(
                      state, true, "Assumed variable '" + memoryLocation + "' was untainted");
            }
          } else if (func.equals("__VERIFIER_assert_tainted")) {
            logger.log(Level.INFO, memoryLocation);
            if (!state.getStatus(memoryLocation)) {
              newElement =
                  TaintAnalysisState.copyOf(
                      state, true, "Assumed variable '" + memoryLocation + "' was tainted");
            }
          } else if (options.isUseCriticalSinkFunctions()) {
            MemoryLocation memoryLocation1 = MemoryLocation.valueOf(functionName, exp.getParameterExpressions().get(1).toString());
            if (func.equals("printf") && state.getStatus(memoryLocation1)
                || func.equals("strcmp")
                || func.equals("fputs")
                || func.equals("fputc")
                || func.equals("fwrite"))
            {
              newElement =
                  TaintAnalysisState.copyOf(
                      state,
                      true,
                      "Critical function '" + func + "' was called with a tainted parameter");
            }
          }
          msg = msg + " | " + param;
        } else {
          msg = msg + " | else: " + expression.getClass();
        }
      }
    }

    // expression is a binary operation, e.g. a = b;

    else if (expression instanceof AAssignment) {
      newElement = handleAssignment((AAssignment) expression, cfaEdge);
      return newElement;

    } else if (expression instanceof AFunctionCallStatement) {
      msg = msg + " | AFunctionCallStatement";

    } else if (expression instanceof AExpressionStatement) {
      msg = msg + " | AExpressionStatement";

    } else {
      throw new UnrecognizedCodeException("Unknown statement", cfaEdge, expression);
    }
    logger.log(Level.INFO, msg);
    return newElement;
  }

  private TaintAnalysisState handleAssignment(AAssignment assignExpression, CFAEdge cfaEdge)
      throws UnrecognizedCodeException {
    TaintAnalysisState newElement = TaintAnalysisState.copyOf(state);
    String msg = "";

    AExpression op1 = assignExpression.getLeftHandSide();
    ARightHandSide op2 = assignExpression.getRightHandSide();
    msg =
        msg
            + op1
            + " = "
            + op2
            + " "
            + op2.getExpressionType();

    if (op1 instanceof AIdExpression) {
      // a = ...
      msg = msg + "\nAIdExpression";
      if (op2 instanceof ALiteralExpression) {
        msg = msg + " | ALiteralExpression";
        MemoryLocation memoryLocation = MemoryLocation.valueOf(functionName, op1.toString());
        newElement.change(memoryLocation, false);
        return newElement;
      } else if (op2 instanceof ABinaryExpression) {
        msg = msg + " | ABinaryExpression";
        ABinaryExpression binOp = (ABinaryExpression) op2;
        msg = msg + " | Operator: "+binOp.getOperator();
        if (binOp.getOperator() == BinaryOperator.MINUS && binOp.getOperand1().toString().equals(binOp.getOperand2().toString())) {
          msg = msg + " | Self sebstract";
          MemoryLocation memoryLocation = MemoryLocation.valueOf(functionName, op1.toString());
          newElement.change(memoryLocation, false);
        } else {
          Boolean result = false;
          MemoryLocation memOp1 = MemoryLocation.valueOf(functionName, binOp.getOperand1().toString());
          MemoryLocation memOp2 = MemoryLocation.valueOf(functionName, binOp.getOperand2().toString());
          if(binOp.getOperand1() instanceof AIdExpression && binOp.getOperand2() instanceof AIdExpression)
            result = state.getStatus(memOp1) || state.getStatus(memOp2);
          else if(binOp.getOperand1() instanceof ALiteralExpression)
            result = state.getStatus(memOp2);
          else if(binOp.getOperand2() instanceof ALiteralExpression)
            result = state.getStatus(memOp1);
          MemoryLocation memoryLocation = MemoryLocation.valueOf(functionName, op1.toString());
          newElement.change(memoryLocation, result);
          msg = msg + " | result: "+result;
        }
      } else {
        if(op1.getExpressionType().toString().indexOf('*') != -1) {
          MemoryLocation memOp1 = MemoryLocation.valueOf(functionName, op1.toString());
          MemoryLocation memOp2 = MemoryLocation.valueOf(functionName, op2.toString());
          newElement.addPointerTo(memOp1, memOp2);
        } else {
          MemoryLocation memOp1 = MemoryLocation.valueOf(functionName, op1.toString());
          MemoryLocation memOp2 = MemoryLocation.valueOf(functionName, op2.toString());
          msg = msg + " | Status op2: " + state.getStatus(memOp2);
          newElement.change(memOp1, newElement.getStatus(memOp2));
          msg = msg + " | Status op1: " + newElement.getStatus(memOp1);
        }
      } // if(op2 instanceof ALiteralExpression)
      // return handleAssignmentToVariable(memloc, op1.getExpressionType(), op2, getVisitor());
    } else if (op1 instanceof APointerExpression) {
      // *a = ...
      msg = msg + "\nAPointerExpression";
      // if (isRelevant(op1, op2)) {
      // missingInformationList.add(new MissingInformation(op1, op2));
      // }

    } else if (op1 instanceof CFieldReference) {
      // ???
      msg = msg + "\nCFieldReference";

    } else if (op1 instanceof AArraySubscriptExpression) {
      // array cell
      msg = msg + " | AArraySubscriptExpression";
      if (op1 instanceof CArraySubscriptExpression) {
        msg = msg + " | CArraySubscriptExpression";
      } else if (op1 instanceof JArraySubscriptExpression) {
        msg = msg + " | JArraySubscriptExpression";
      }
    } else {
      throw new UnrecognizedCodeException(
          "left operand of assignment has to be a variable", cfaEdge, op1);
    }

    logger.log(Level.INFO, msg);
    return newElement; // the default return-value is the old state
  }

  // private boolean isTrackedType(Type pType) {
  // return !(pType instanceof JType)
  // || options.trackJavaArrayValues
  // || !(pType instanceof JArrayType);
  // }

  /**
   * This method analyses the expression with the visitor and assigns the value to lParam. The
   * method returns a new state, that contains (a copy of) the old state and the new assignment.
   */
  // private TaintAnalysisState handleAssignmentToVariable(
  // MemoryLocation assignedVar, final Type lType, ARightHandSide exp, ExpressionValueVisitor
  // visitor)
  // throws UnrecognizedCodeException {
  // // here we clone the state, because we get new information or must forget it.
  // TaintAnalysisState newElement = TaintAnalysisState.copyOf(state);
  // handleAssignmentToVariable(newElement, assignedVar, lType, exp, visitor);
  // return newElement;
  // }

  /**
   * This method analyses the expression with the visitor and assigns the value to lParam to the
   * given value Analysis state.
   */
  // private void handleAssignmentToVariable(TaintAnalysisState newElement,
  // MemoryLocation assignedVar, final Type lType, ARightHandSide exp, ExpressionValueVisitor
  // visitor)
  // throws UnrecognizedCodeException {

  // // c structs have to be handled seperatly, because we do not have a value object representing
  // structs
  // if (lType instanceof CType) {
  // CType canonicaltype = ((CType) lType).getCanonicalType();
  // if (canonicaltype instanceof CCompositeType
  // && ((CCompositeType) canonicaltype).getKind() == ComplexTypeKind.STRUCT
  // && exp instanceof CLeftHandSide) {
  // handleAssignmentToStruct(newElement, assignedVar, (CCompositeType) canonicaltype, (CExpression)
  // exp, visitor);
  // return;
  // }
  // }

  // Value value;
  // if (exp instanceof JRightHandSide) {
  // value = visitor.evaluate((JRightHandSide) exp, (JType) lType);
  // } else if (exp instanceof CRightHandSide) {
  // value = visitor.evaluate((CRightHandSide) exp, (CType) lType);
  // } else {
  // throw new AssertionError("unknown righthandside-expression: " + exp);
  // }

  // if (visitor.hasMissingPointer()) {
  // assert !value.isExplicitlyKnown();
  // }

  // if (isMissingCExpressionInformation(visitor, exp)) {
  // // Evaluation
  // addMissingInformation(assignedVar, exp);
  // }

  // if (visitor.hasMissingFieldAccessInformation()) {
  // // This may happen if an object of class is created which could not be parsed,
  // // In such a case, forget about it
  // if (!value.isUnknown()) {
  // newElement.forget(assignedVar);
  // return;
  // } else {
  // missingInformationRightJExpression = (JRightHandSide) exp;
  // if (!missingScopedFieldName) {
  // missingInformationLeftJVariable = assignedVar.getAsSimpleString();
  // }
  // }
  // }

  // if (missingScopedFieldName) {
  // notScopedFieldValue = value;
  // } else {
  // // some heuristics to clear wrong information
  // // when a struct or a pointer to one is assigned
  // // TODO not implemented in SMG version of ValueAnalysisCPA
  // // newElement.forgetAllWithPrefix(assignedVar + ".");
  // // newElement.forgetAllWithPrefix(assignedVar + "->");

  // // if there is no information left to evaluate but the value is unknown, we assign a symbolic
  // // identifier to keep track of the variable.
  // if (value.isUnknown()) {
  // unknownValueHandler.handle(assignedVar, lType, newElement, visitor);

  // } else {
  // newElement.assignConstant(assignedVar, value, lType);
  // }
  // }
  // }

  /**
   * This method transforms the assignment of the struct into assignments of its respective field
   * references and assigns them to the given value state.
   */
  // private void handleAssignmentToStruct(TaintAnalysisState pNewElement,
  // MemoryLocation pAssignedVar,
  // CCompositeType pLType, CExpression pExp,
  // ExpressionValueVisitor pVisitor) throws UnrecognizedCodeException {

  // long offset = 0L;
  // for (CCompositeType.CCompositeTypeMemberDeclaration memberType : pLType.getMembers()) {
  // MemoryLocation assignedField = createFieldMemoryLocation(pAssignedVar, offset);

  // CExpression owner = pExp;

  // CExpression fieldReference =
  // new CFieldReference(pExp.getFileLocation(), memberType.getType(), memberType.getName(), owner,
  // false);
  // handleAssignmentToVariable(pNewElement, assignedField, memberType.getType(), fieldReference,
  // pVisitor);

  // offset = offset + machineModel.getSizeof(memberType.getType()).longValueExact();
  // }
  // }

  // private void addMissingInformation(MemoryLocation pMemLoc, ARightHandSide pExp) {
  // if (pExp instanceof CExpression) {

  // missingInformationList.add(new MissingInformation(pMemLoc,
  // (CExpression) pExp));
  // }
  // }

  // private void addMissingInformation(CLeftHandSide pOp1, Value pValue) {
  // missingInformationList.add(new MissingInformation(pOp1, pValue));

  // }

  /**
   * Returns the {@link ArrayValue} object that represents the innermost array of the given {@link
   * JArraySubscriptExpression}.
   *
   * @param pArraySubscriptExpression the subscript expression to get the inner most array of
   * @return <code>null</code> if the complete array or a part significant for the given array
   *     subscript expression is unknown, the <code>ArrayValue</code> representing the innermost
   *     array, otherwise
   */
  // private @Nullable ArrayValue getInnerMostArray(JArraySubscriptExpression
  // pArraySubscriptExpression) {
  // JExpression arrayExpression = pArraySubscriptExpression.getArrayExpression();

  // if (arrayExpression instanceof JIdExpression) {
  // JSimpleDeclaration arrayDeclaration = ((JIdExpression) arrayExpression).getDeclaration();

  // if (arrayDeclaration != null) {
  // MemoryLocation idName = MemoryLocation.valueOf(arrayDeclaration.getQualifiedName());

  // if (state.contains(idName)) {
  // Value idValue = state.getValueFor(idName);
  // if (idValue.isExplicitlyKnown()) {
  // return (ArrayValue) idValue;
  // }
  // }
  // }

  // return null;
  // } else {
  // final JArraySubscriptExpression arraySubscriptExpression = (JArraySubscriptExpression)
  // arrayExpression;
  // // the array enclosing the array specified in the given array subscript expression
  // ArrayValue enclosingArray = getInnerMostArray(arraySubscriptExpression);

  // OptionalInt maybeIndex = getIndex(arraySubscriptExpression);
  // int index;

  // if (maybeIndex.isPresent() && enclosingArray != null) {

  // index = maybeIndex.orElseThrow();

  // } else {
  // return null;
  // }

  // if (index >= enclosingArray.getArraySize() || index < 0) {
  // return null;
  // }

  // return (ArrayValue) enclosingArray.getValueAt(index);
  // }
  // }

  // private void handleAssignmentToArray(ArrayValue pArray, int index, ARightHandSide exp) {
  // assert exp instanceof JExpression;

  // pArray.setValue(((JExpression) exp).accept(getVisitor()), index);
  // }

  // private void assignUnknownValueToEnclosingInstanceOfArray(JArraySubscriptExpression
  // pArraySubscriptExpression) {

  // JExpression enclosingExpression = pArraySubscriptExpression.getArrayExpression();

  // if (enclosingExpression instanceof JIdExpression) {
  // JIdExpression idExpression = (JIdExpression) enclosingExpression;
  // MemoryLocation memLoc = getMemoryLocation(idExpression);
  // Value unknownValue = UnknownValue.getInstance();

  // state.assignConstant(memLoc, unknownValue, JSimpleType.getUnspecified());

  // } else {
  // JArraySubscriptExpression enclosingSubscriptExpression = (JArraySubscriptExpression)
  // enclosingExpression;
  // ArrayValue enclosingArray = getInnerMostArray(enclosingSubscriptExpression);
  // OptionalInt maybeIndex = getIndex(enclosingSubscriptExpression);

  // if (maybeIndex.isPresent() && enclosingArray != null) {
  // enclosingArray.setValue(UnknownValue.getInstance(), maybeIndex.orElseThrow());

  // }
  // // if the index of unknown array in the enclosing array is also unknown, we assign unknown at
  // this array's
  // // position in the enclosing array
  // else {
  // assignUnknownValueToEnclosingInstanceOfArray(enclosingSubscriptExpression);
  // }
  // }
  // }

  // private class FieldAccessExpressionValueVisitor extends ExpressionValueVisitor {
  // private final RTTState jortState;

  // public FieldAccessExpressionValueVisitor(RTTState pJortState, TaintAnalysisState pState) {
  // super(pState, functionName, machineModel, logger);
  // jortState = pJortState;
  // }

  // @Override
  // public Value visit(JBinaryExpression binaryExpression) {
  // return super.visit(binaryExpression);
  // }

  // private String handleIdExpression(JIdExpression expr) {

  // JSimpleDeclaration decl = expr.getDeclaration();

  // if (decl == null) {
  // return null;
  // }

  // NameProvider nameProvider = NameProvider.getInstance();
  // String objectScope = nameProvider.getObjectScope(jortState, functionName, expr);

  // return nameProvider.getScopedVariableName(decl, functionName, objectScope);
  // }

  // @Override
  // public Value visit(JIdExpression idExp) {

  // MemoryLocation varName = MemoryLocation.valueOf(handleIdExpression(idExp));

  // if (readableState.contains(varName)) {
  // return readableState.getValueFor(varName);
  // } else {
  // return Value.UnknownValue.getInstance();
  // }
  // }
  // }

  // private Value getExpressionValue(
  // AExpression expression, final Type type, ExpressionValueVisitor evv)
  // throws UnrecognizedCodeException {
  // if (!isTrackedType(type)) {
  // return UnknownValue.getInstance();
  // }

  // if (expression instanceof JRightHandSide) {

  // final Value value = evv.evaluate((JRightHandSide) expression, (JType) type);

  // if (evv.hasMissingFieldAccessInformation()) {
  // missingInformationRightJExpression = (JRightHandSide) expression;
  // return Value.UnknownValue.getInstance();
  // } else {
  // return value;
  // }
  // } else if (expression instanceof CRightHandSide) {
  // return evv.evaluate((CRightHandSide) expression, (CType) type);
  // } else {
  // throw new AssertionError("unhandled righthandside-expression: " + expression);
  // }
  // }

  // @Override
  // public Collection<? extends AbstractState> strengthen(
  // AbstractState pElement,
  // Iterable<AbstractState> pElements,
  // CFAEdge pCfaEdge,
  // Precision pPrecision)
  // throws CPATransferException {
  // assert pElement instanceof TaintAnalysisState;

  // List<TaintAnalysisState> toStrengthen = new ArrayList<>();
  // List<TaintAnalysisState> result = new ArrayList<>();
  // toStrengthen.add((TaintAnalysisState) pElement);
  // result.add((TaintAnalysisState) pElement);

  // for (AbstractState ae : pElements) {
  // if (ae instanceof RTTState) {
  // result.clear();
  // for (TaintAnalysisState stateToStrengthen : toStrengthen) {
  // super.setInfo(pElement, pPrecision, pCfaEdge);
  // Collection<TaintAnalysisState> ret = strengthen((RTTState)ae, pCfaEdge);
  // if (ret == null) {
  // result.add(stateToStrengthen);
  // } else {
  // result.addAll(ret);
  // }
  // }
  // toStrengthen.clear();
  // toStrengthen.addAll(result);
  // } else if (ae instanceof AbstractStateWithAssumptions) {
  // result.clear();
  // for (TaintAnalysisState stateToStrengthen : toStrengthen) {
  // super.setInfo(pElement, pPrecision, pCfaEdge);
  // AbstractStateWithAssumptions stateWithAssumptions = (AbstractStateWithAssumptions) ae;
  // result.addAll(
  // strengthenWithAssumptions(stateWithAssumptions, stateToStrengthen, pCfaEdge));
  // }
  // toStrengthen.clear();
  // toStrengthen.addAll(result);
  // } else if (ae instanceof ThreadingState) {
  // result.clear();
  // for (TaintAnalysisState stateToStrengthen : toStrengthen) {
  // super.setInfo(pElement, pPrecision, pCfaEdge);
  // result.add(strengthenWithThreads((ThreadingState) ae, stateToStrengthen));
  // }
  // toStrengthen.clear();
  // toStrengthen.addAll(result);
  // } else if (ae instanceof ConstraintsState) {
  // result.clear();

  // for (TaintAnalysisState stateToStrengthen : toStrengthen) {
  // super.setInfo(pElement, pPrecision, pCfaEdge);
  // Collection<TaintAnalysisState> ret =
  // constraintsStrengthenOperator.strengthen((TaintAnalysisState) pElement, (ConstraintsState) ae,
  // pCfaEdge);

  // if (ret == null) {
  // result.add(stateToStrengthen);
  // } else {
  // result.addAll(ret);
  // }
  // }
  // toStrengthen.clear();
  // toStrengthen.addAll(result);
  // } else if (ae instanceof PointerState) {

  // CFAEdge edge = pCfaEdge;

  // ARightHandSide rightHandSide = CFAEdgeUtils.getRightHandSide(edge);
  // ALeftHandSide leftHandSide = CFAEdgeUtils.getLeftHandSide(edge);
  // Type leftHandType = CFAEdgeUtils.getLeftHandType(edge);
  // String leftHandVariable = CFAEdgeUtils.getLeftHandVariable(edge);
  // PointerState pointerState = (PointerState) ae;

  // result.clear();

  // for (TaintAnalysisState stateToStrengthen : toStrengthen) {
  // super.setInfo(pElement, pPrecision, pCfaEdge);
  // TaintAnalysisState newState =
  // strengthenWithPointerInformation(stateToStrengthen, pointerState, rightHandSide, leftHandType,
  // leftHandSide, leftHandVariable, UnknownValue.getInstance());

  // newState = handleModf(rightHandSide, pointerState, newState);

  // result.add(newState);
  // }
  // toStrengthen.clear();
  // toStrengthen.addAll(result);
  // }

  // }

  // // Do post processing
  // final Collection<AbstractState> postProcessedResult = new ArrayList<>(result.size());
  // for (TaintAnalysisState rawResult : result) {
  // // The original state has already been post-processed
  // if (rawResult == pElement) {
  // postProcessedResult.add(pElement);
  // } else {
  // postProcessedResult.addAll(postProcessing(rawResult, pCfaEdge));
  // }
  // }

  // super.resetInfo();
  // oldState = null;

  // return postProcessedResult;
  // }

  /**
   * Handle a special built-in library function that required pointer-alias handling while computing
   * a floating-point operation.
   *
   * @param pRightHandSide the right-hand side of an assignment edge.
   * @param pPointerState the current pointer-alias information.
   * @param pState the state to strengthen.
   * @return the strengthened state.
   * @throws UnrecognizedCodeException if the C code involved is not recognized.
   */
  // private TaintAnalysisState handleModf(
  // ARightHandSide pRightHandSide, PointerState pPointerState, TaintAnalysisState pState)
  // throws UnrecognizedCodeException, AssertionError {
  // TaintAnalysisState newState = pState;
  // if (pRightHandSide instanceof AFunctionCallExpression) {
  // AFunctionCallExpression functionCallExpression = (AFunctionCallExpression) pRightHandSide;
  // AExpression nameExpressionOfCalledFunc = functionCallExpression.getFunctionNameExpression();
  // if (nameExpressionOfCalledFunc instanceof AIdExpression) {
  // String nameOfCalledFunc = ((AIdExpression) nameExpressionOfCalledFunc).getName();
  // if (BuiltinFloatFunctions.matchesModf(nameOfCalledFunc)) {
  // List<? extends AExpression> parameters = functionCallExpression.getParameterExpressions();
  // if (parameters.size() == 2 && parameters.get(1) instanceof CExpression) {
  // AExpression exp = parameters.get(0);
  // CExpression targetPointer = (CExpression) parameters.get(1);
  // CLeftHandSide target =
  // new CPointerExpression(
  // targetPointer.getFileLocation(),
  // targetPointer.getExpressionType(),
  // targetPointer);
  // ExpressionValueVisitor evv = getVisitor();
  // Value value;
  // if (exp instanceof JRightHandSide) {
  // value = evv.evaluate((JRightHandSide) exp, (JType) exp.getExpressionType());
  // } else if (exp instanceof CRightHandSide) {
  // value = evv.evaluate((CRightHandSide) exp, (CType) exp.getExpressionType());
  // } else {
  // throw new AssertionError("unknown righthandside-expression: " + exp);
  // }
  // if (value.isExplicitlyKnown()) {
  // NumericValue numericValue = value.asNumericValue();
  // CSimpleType paramType =
  // BuiltinFloatFunctions.getTypeOfBuiltinFloatFunction(nameOfCalledFunc);
  // if (ImmutableList.of(CBasicType.FLOAT, CBasicType.DOUBLE)
  // .contains(paramType.getType())) {
  // final BigDecimal integralPartValue;
  // switch (paramType.getType()) {
  // case FLOAT:
  // integralPartValue = BigDecimal.valueOf((float) ((long) numericValue.floatValue()));
  // break;
  // case DOUBLE:
  // integralPartValue = BigDecimal.valueOf((double) ((long) numericValue.doubleValue()));
  // break;
  // default:
  // throw new AssertionError("Unsupported float type: " + paramType);
  // }
  // CFloatLiteralExpression integralPart =
  // new CFloatLiteralExpression(
  // functionCallExpression.getFileLocation(),
  // paramType,
  // integralPartValue);
  // newState =
  // strengthenWithPointerInformation(
  // newState,
  // pPointerState,
  // integralPart,
  // target.getExpressionType(),
  // target,
  // null,
  // new NumericValue(integralPartValue));
  // }
  // }
  // }
  // }
  // }
  // }
  // return newState;
  // }

  // private TaintAnalysisState strengthenWithPointerInformation(
  // TaintAnalysisState pValueState,
  // PointerState pPointerInfo,
  // ARightHandSide pRightHandSide,
  // Type pTargetType,
  // ALeftHandSide pLeftHandSide,
  // String pLeftHandVariable,
  // Value pValue)
  // throws UnrecognizedCodeException {

  // TaintAnalysisState newState = pValueState;

  // Value value = pValue;
  // MemoryLocation target = null;
  // if (pLeftHandVariable != null) {
  // target = MemoryLocation.valueOf(pLeftHandVariable);
  // }
  // Type type = pTargetType;
  // boolean shouldAssign = false;

  // if (target == null && pLeftHandSide instanceof CPointerExpression) {
  // CPointerExpression pointerExpression = (CPointerExpression) pLeftHandSide;

  // LocationSet directLocation =
  // PointerTransferRelation.asLocations(pointerExpression, pPointerInfo);

  // if (!(directLocation instanceof ExplicitLocationSet)) {
  // CExpression addressExpression = pointerExpression.getOperand();
  // LocationSet indirectLocation =
  // PointerTransferRelation.asLocations(addressExpression, pPointerInfo);
  // if (indirectLocation instanceof ExplicitLocationSet) {
  // ExplicitLocationSet explicitSet = (ExplicitLocationSet) indirectLocation;
  // if (explicitSet.getSize() == 1) {
  // MemoryLocation variable = explicitSet.iterator().next();
  // directLocation = pPointerInfo.getPointsToSet(variable);
  // }
  // }
  // }
  // if (directLocation instanceof ExplicitLocationSet) {
  // ExplicitLocationSet explicitDirectLocation = (ExplicitLocationSet) directLocation;
  // Iterator<MemoryLocation> locationIterator = explicitDirectLocation.iterator();
  // MemoryLocation otherVariable = locationIterator.next();
  // if (!locationIterator.hasNext()) {
  // target = otherVariable;
  // if (type == null && pValueState.contains(target)) {
  // type = pValueState.getTypeForMemoryLocation(target);
  // }
  // shouldAssign = true;
  // }
  // }

  // }

  // if (!value.isExplicitlyKnown() && pRightHandSide instanceof CPointerExpression) {
  // if (target == null) {
  // return pValueState;
  // }

  // CPointerExpression rhs = (CPointerExpression) pRightHandSide;
  // CExpression addressExpression = rhs.getOperand();

  // LocationSet fullSet = PointerTransferRelation.asLocations(addressExpression, pPointerInfo);

  // if (fullSet instanceof ExplicitLocationSet) {
  // ExplicitLocationSet explicitSet = (ExplicitLocationSet) fullSet;
  // if (explicitSet.getSize() == 1) {
  // MemoryLocation variable = explicitSet.iterator().next();
  // CType variableType = rhs.getExpressionType().getCanonicalType();
  // LocationSet pointsToSet = pPointerInfo.getPointsToSet(variable);

  // if (pointsToSet instanceof ExplicitLocationSet) {
  // ExplicitLocationSet explicitPointsToSet = (ExplicitLocationSet) pointsToSet;
  // Iterator<MemoryLocation> pointsToIterator = explicitPointsToSet.iterator();
  // MemoryLocation otherVariableLocation = pointsToIterator.next();
  // if (!pointsToIterator.hasNext() && pValueState.contains(otherVariableLocation)) {

  // ValueAndType valueAndType = pValueState.getValueAndTypeFor(otherVariableLocation);
  // Type otherVariableType = valueAndType.getType();
  // if (otherVariableType != null) {
  // Value otherVariableValue = valueAndType.getValue();
  // if (otherVariableValue != null) {
  // if (variableType.equals(otherVariableType)
  // || (variableType.equals(CNumericTypes.FLOAT)
  // && otherVariableType.equals(CNumericTypes.UNSIGNED_INT)
  // && otherVariableValue.isExplicitlyKnown()
  // && Long.valueOf(0)
  // .equals(otherVariableValue.asLong(CNumericTypes.UNSIGNED_INT)))) {
  // value = otherVariableValue;
  // shouldAssign = true;
  // }
  // }
  // }
  // }
  // }
  // }
  // }
  // }

  // if (target != null && type != null && shouldAssign) {
  // newState = TaintAnalysisState.copyOf(pValueState);
  // newState.assignConstant(target, value, type);
  // }

  // return newState;
  // }

  // private @NonNull Collection<TaintAnalysisState> strengthenWithAssumptions(
  // AbstractStateWithAssumptions pStateWithAssumptions,
  // TaintAnalysisState pState,
  // CFAEdge pCfaEdge)
  // throws CPATransferException {

  // TaintAnalysisState newState = pState;

  // for (AExpression assumption : pStateWithAssumptions.getAssumptions()) {
  // newState = handleAssumption(assumption, true);

  // if (newState == null) {
  // break;
  // } else {
  // setInfo(newState, precision, pCfaEdge);
  // }
  // }

  // if (newState == null) {
  // return ImmutableList.of();
  // } else {
  // return Collections.singleton(newState);
  // }
  // }

  // private @NonNull TaintAnalysisState strengthenWithThreads(
  // ThreadingState pThreadingState, TaintAnalysisState pState) throws CPATransferException {
  // final FunctionCallEdge function = pThreadingState.getEntryFunction();
  // if (function == null) {
  // return pState;
  // }
  // final FunctionEntryNode succ = function.getSuccessor();
  // final String calledFunctionName = succ.getFunctionName();
  // return handleFunctionCallEdge(
  // function, function.getArguments(), succ.getFunctionParameters(), calledFunctionName);
  // }

  // private Collection<TaintAnalysisState> strengthen(RTTState rttState, CFAEdge edge) {

  // TaintAnalysisState newElement = TaintAnalysisState.copyOf(oldState);

  // if (missingFieldVariableObject) {
  // newElement.assignConstant(getRTTScopedVariableName(
  // fieldNameAndInitialValue.getFirst(),
  // rttState.getKeywordThisUniqueObject()),
  // fieldNameAndInitialValue.getSecond());

  // missingFieldVariableObject = false;
  // fieldNameAndInitialValue = null;
  // return Collections.singleton(newElement);

  // } else if (missingScopedFieldName) {

  // newElement = handleNotScopedVariable(rttState, newElement);
  // missingScopedFieldName = false;
  // notScopedField = null;
  // notScopedFieldValue = null;
  // missingInformationRightJExpression = null;

  // if (newElement != null) {
  // return Collections.singleton(newElement);
  // } else {
  // return null;
  // }
  // } else if (missingAssumeInformation && missingInformationRightJExpression != null) {

  // Value value = handleMissingInformationRightJExpression(rttState);

  // missingAssumeInformation = false;
  // missingInformationRightJExpression = null;

  // boolean truthAssumption = ((AssumeEdge)edge).getTruthAssumption();
  // if (value == null || !value.isExplicitlyKnown()) {
  // return null;
  // } else if (representsBoolean(value, truthAssumption)) {
  // return Collections.singleton(newElement);
  // } else {
  // return new HashSet<>();
  // }
  // } else if (missingInformationRightJExpression != null) {

  // Value value = handleMissingInformationRightJExpression(rttState);

  // if (!value.isUnknown()) {
  // newElement.assignConstant(missingInformationLeftJVariable, value);
  // missingInformationRightJExpression = null;
  // missingInformationLeftJVariable = null;
  // return Collections.singleton(newElement);
  // } else {
  // if (missingInformationLeftJVariable != null) {
  // newElement.forget(MemoryLocation.valueOf(missingInformationLeftJVariable));
  // }
  // missingInformationRightJExpression = null;
  // missingInformationLeftJVariable = null;
  // return Collections.singleton(newElement);
  // }
  // }
  // return null;
  // }

  // private String getRTTScopedVariableName(String fieldName, String uniqueObject) {
  // return uniqueObject + "::"+ fieldName;
  // }

  // private Value handleMissingInformationRightJExpression(RTTState pJortState) {
  // return missingInformationRightJExpression.accept(
  // new FieldAccessExpressionValueVisitor(pJortState, oldState));
  // }

  // private TaintAnalysisState handleNotScopedVariable(RTTState rttState, TaintAnalysisState
  // newElement) {

  // String objectScope = NameProvider.getInstance()
  // .getObjectScope(rttState, functionName, notScopedField);

  // if (objectScope != null) {

  // String scopedFieldName = getRTTScopedVariableName(notScopedField.getName(), objectScope);

  // Value value = notScopedFieldValue;
  // if (missingInformationRightJExpression != null) {
  // value = handleMissingInformationRightJExpression(rttState);
  // }

  // if (!value.isUnknown()) {
  // newElement.assignConstant(scopedFieldName, value);
  // return newElement;
  // } else {
  // newElement.forget(MemoryLocation.valueOf(scopedFieldName));
  // return newElement;
  // }
  // } else {
  // return null;
  // }

  // }

  // /** returns an initialized, empty visitor */
  // private ExpressionValueVisitor getVisitor(TaintAnalysisState pState, String pFunctionName) {
  // if (options.isIgnoreFunctionValueExceptRandom()
  // && options.isIgnoreFunctionValue()
  // && options.getFunctionValuesForRandom() != null) {
  // return new ExpressionValueVisitorWithPredefinedValues(
  // pState,
  // pFunctionName,
  // options.getFunctionValuesForRandom(),
  // ValueAnalysisTransferRelation.indexForNextRandomValue,
  // machineModel,
  // logger);
  // } else if (options.isIgnoreFunctionValue()) {
  // return new ExpressionValueVisitor(pState, pFunctionName, machineModel, logger);
  // } else {
  // return new FunctionPointerExpressionValueVisitor(pState, pFunctionName, machineModel, logger);
  // }
  // }

  // private ExpressionValueVisitor getVisitor() {
  // return getVisitor(state, functionName);
  // }
}
