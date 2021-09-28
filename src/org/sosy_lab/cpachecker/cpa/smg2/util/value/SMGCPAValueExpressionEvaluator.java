// This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.cpachecker.cpa.smg2.util.value;

import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.Collection;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManagerWithoutDuplicates;
import org.sosy_lab.cpachecker.cfa.ast.c.CArraySubscriptExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CFieldReference;
import org.sosy_lab.cpachecker.cfa.ast.c.CIdExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CPointerExpression;
import org.sosy_lab.cpachecker.cfa.ast.c.CRightHandSide;
import org.sosy_lab.cpachecker.cfa.ast.java.JClassLiteralExpression;
import org.sosy_lab.cpachecker.cfa.ast.java.JIdExpression;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.cfa.types.c.CArrayType;
import org.sosy_lab.cpachecker.cfa.types.c.CComplexType;
import org.sosy_lab.cpachecker.cfa.types.c.CCompositeType;
import org.sosy_lab.cpachecker.cfa.types.c.CElaboratedType;
import org.sosy_lab.cpachecker.cfa.types.c.CFunctionType;
import org.sosy_lab.cpachecker.cfa.types.c.CPointerType;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.cpa.smg.TypeUtils;
import org.sosy_lab.cpachecker.cpa.smg2.SMGState;
import org.sosy_lab.cpachecker.cpa.value.AbstractExpressionValueVisitor;
import org.sosy_lab.cpachecker.cpa.value.type.Value;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.NoException;
import org.sosy_lab.cpachecker.exceptions.UnrecognizedCodeException;
import org.sosy_lab.cpachecker.util.smg.graph.SMGObject;

@SuppressWarnings("unused")
public class SMGCPAValueExpressionEvaluator extends AbstractExpressionValueVisitor
    implements AddressEvaluator {

  public SMGCPAValueExpressionEvaluator(
      String pFunctionName,
      MachineModel pMachineModel,
      LogManagerWithoutDuplicates pLogger) {
    super(pFunctionName, pMachineModel, pLogger);
  }

  @Override
  protected Value evaluateCPointerExpression(CPointerExpression pCPointerExpression)
      throws UnrecognizedCodeException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Value evaluateCIdExpression(CIdExpression pCIdExpression)
      throws UnrecognizedCodeException {
    // TODO Auto-generated method stub
    return null;
  }



  @Override
  protected Value evaluateCFieldReference(CFieldReference pLValue)
      throws UnrecognizedCodeException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Value evaluateCArraySubscriptExpression(CArraySubscriptExpression pLValue)
      throws UnrecognizedCodeException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Value visit(JClassLiteralExpression pJClassLiteralExpression) throws NoException {
    return throwUnsupportedOperationException("visit(JClassLiteralExpression)");
  }

  @Override
  protected Value evaluateJIdExpression(JIdExpression pVarName) {
    return throwUnsupportedOperationException("evaluateJIdExpression");
  }

  private Value throwUnsupportedOperationException(String methodNameString) {
    throw new AssertionError("The operation " + methodNameString + " is not yet supported.");
  }

  public Collection<SMGState> evaluateValues(
      SMGState pState,
      CFAEdge cfaEdge,
      CRightHandSide rValue)
      throws CPATransferException {
    return null;
  }

  public Collection<CValueAndSMGState>
      evaluateExpressionValue(SMGState smgState, CFAEdge cfaEdge, CRightHandSide rValue)
          throws CPATransferException {
    if (isAddressType(rValue.getExpressionType())) {
      /*
       * expressions with Array Types as result are transformed. a = &(a[0])
       */

      /*
       * expressions with structs or unions as result will be evaluated to their addresses. The
       * address can be used e.g. to copy the struct.
       */
      return evaluateAddress(smgState, cfaEdge, rValue);
    } else {
      // derive value
      return rValue.accept(new NonPointerExpressionVisitor(smgState, this));
    }
  }

  private Collection<CValueAndSMGState>
      evaluateAddress(SMGState pSmgState, CFAEdge pCfaEdge, CRightHandSide pRValue) {
    // TODO Auto-generated method stub
    return null;
  }

  public static boolean isAddressType(CType cType) {
    if (cType instanceof CElaboratedType) {
      CElaboratedType type = (CElaboratedType) cType;
      return type.getKind() != CComplexType.ComplexTypeKind.ENUM;
    }

    if (cType instanceof CCompositeType) {
      CCompositeType type = (CCompositeType) cType;
      return type.getKind() != CComplexType.ComplexTypeKind.ENUM;
    }
    return cType instanceof CPointerType
        || cType instanceof CArrayType
        || cType instanceof CFunctionType;
  }

  @Override
  public Collection<CValueAndSMGState>
      evaluateArraySubscriptAddress(SMGState pInitialSmgState, CExpression pExp) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Collection<CValueAndSMGState>
      evaluateAddress(SMGState pInitialSmgState, CExpression pOperand) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Collection<CValueAndSMGState>
      evaluateArrayAddress(SMGState pInitialSmgState, CExpression pOperand) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Collection<CValueAndSMGState>
      createAddress(SMGState pState, CValue pValue) {
    // TODO Auto-generated method stub
    return null;
  }


  @Override
  public CValueAndSMGState readValue(SMGState pState, CValue value, CExpression pExp) {
    return readValue(pState, pState.getPointsToTarget(value), value, pExp);
  }

  public CValueAndSMGState
      readValue(SMGState pState, SMGObject object, CValue value, CExpression pExpression) {
    if (value.isUnknown() || object.isZero()) {
      return CValueAndSMGState.ofUnknown(pState);
    }

    BigInteger fieldOffset = value.getExplicitValue();

    // FIXME Does not work with variable array length.
    boolean doesNotFitIntoObject =
        fieldOffset.compareTo(BigInteger.ZERO) < 0
            || fieldOffset.add(getBitSizeof(pState, pExpression)).compareTo(object.getSize()) > 0;

    if (doesNotFitIntoObject) {
      // Field does not fit size of declared Memory
      getLogger().log(
          Level.WARNING,
          pExpression.getFileLocation() + ":",
          "Field "
              + "("
              + fieldOffset
              + ", "
              + pExpression.getExpressionType().toASTString("")
              + ")"
              + " does not fit object "
              + object
              + ".");

      return CValueAndSMGState.ofUnknown(pState);
    }
    CType type = TypeUtils.getRealExpressionType(pExpression);

    return pState.readValue(
            object,
            fieldOffset,
        getMachineModel().getSizeofInBits(type));
  }

  @Override
  public Collection<CValueAndSMGState>
      getAddressOfField(SMGState pInitialSmgState, CFieldReference pExpression) {
    CExpression fieldOwner = pExpression.getFieldOwner();
    CType ownerType = TypeUtils.getRealExpressionType(fieldOwner);
    return evaluateAddress(pInitialSmgState, fieldOwner).stream().map(addressAndState -> {
      CValue addressCValue = addressAndState.getValue();
      SMGState state = addressAndState.getState();
      String fieldName = pExpression.getFieldName();
      CValue fieldOffset = getFieldOffset(ownerType, fieldName);
      if (fieldOffset.isUnknown() || addressCValue.isUnknown()) {
        if (pExpression.isPointerDereference()) {
          state = handleUnknownDereference(state).getState();
        }
        fieldOffset = fieldOffset.add(addressCValue);
        return CValueAndSMGState.of(fieldOffset, state);
      }

      return CValueAndSMGState.ofUnknown(state);
    }).collect(ImmutableSet.toImmutableSet());
  }

  private CValue getFieldOffset(CType pType, String pFieldName) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CValueAndSMGState handleUnknownDereference(SMGState pInitialSmgState) {
    return CValueAndSMGState.ofUnknown(pInitialSmgState);
  }

  @Override
  public CValueAndSMGState
      readValue(SMGState pSmgState, SMGObject pVariableObject, CExpression pExpression) {
    return readValue(pSmgState, pVariableObject, CValue.zero(), pExpression);
  }

  @Override
  public BigInteger getBitSizeof(SMGState pInitialSmgState, CExpression pExpression) {
    // TODO check why old implementation did not use machineModel
    return getMachineModel().getSizeofInBits(pExpression.getExpressionType());
  }


}
