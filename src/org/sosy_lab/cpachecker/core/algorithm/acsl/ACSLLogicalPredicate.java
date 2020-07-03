package org.sosy_lab.cpachecker.core.algorithm.acsl;

import com.google.common.base.Preconditions;
import org.sosy_lab.cpachecker.util.expressions.And;
import org.sosy_lab.cpachecker.util.expressions.ExpressionTree;
import org.sosy_lab.cpachecker.util.expressions.Or;

public class ACSLLogicalPredicate extends ACSLPredicate {

  private final ACSLPredicate left;
  private final ACSLPredicate right;
  private final BinaryOperator operator;

  public ACSLLogicalPredicate(ACSLPredicate pLeft, ACSLPredicate pRight, BinaryOperator op) {
    super();
    left = pLeft;
    right = pRight;
    Preconditions.checkArgument(
        BinaryOperator.isLogicOperator(op), "Unknown logic operator: %s", op);
    operator = op;
  }

  @Override
  public String toString() {
    String positiveTemplate = "(%s)";
    String negativeTemplate = "!(%s)";
    String template = isNegated() ? negativeTemplate : positiveTemplate;
    return String.format(template, left.toString() + operator.toString() + right.toString());
  }

  @Override
  public ACSLPredicate toPureC() {
    ACSLPredicate pureLeft = left.toPureC();
    ACSLPredicate pureRight = right.toPureC();
    BinaryOperator newOperator = operator;
    switch (operator) {
      case AND:
      case OR:
        // these are already C operators
        break;
      case XOR:
        ACSLPredicate notRight = pureRight.getCopy().negate();
        ACSLPredicate notLeft = pureLeft.getCopy().negate();
        pureLeft = new ACSLLogicalPredicate(pureLeft, notRight, BinaryOperator.AND);
        pureRight = new ACSLLogicalPredicate(notLeft, pureRight, BinaryOperator.AND);
        newOperator = BinaryOperator.OR;
        break;
      case IMP:
        pureLeft.negate();
        newOperator = BinaryOperator.OR;
        break;
      case EQV:
        ACSLPredicate negL = pureLeft.getCopy().negate();
        ACSLPredicate negR = pureRight.getCopy().negate();
        pureLeft = new ACSLLogicalPredicate(pureLeft, pureRight, BinaryOperator.AND);
        pureRight = new ACSLLogicalPredicate(negL, negR, BinaryOperator.AND);
        newOperator = BinaryOperator.OR;
        break;
      default:
        throw new AssertionError("Unknown logical operator: " + operator);
    }
    return new ACSLLogicalPredicate(pureLeft, pureRight, newOperator);
  }

  @Override
  public ACSLPredicate getCopy() {
    return new ACSLLogicalPredicate(left.getCopy(), right.getCopy(), operator);
  }

  @Override
  public ACSLPredicate simplify() {
    ACSLPredicate simpleLeft = left.simplify();
    ACSLPredicate simpleRight = right.simplify();
    switch (operator) {
      case AND:
        if (simpleLeft.equals(getFalse())
            || simpleRight.equals(getFalse())
            || simpleLeft.isNegationOf(simpleRight)) {
          return getFalse();
        } else if (simpleLeft.equals(simpleRight)) {
          return simpleLeft;
        } else if (simpleLeft.equals(getTrue())) {
          return simpleRight;
        } else if (simpleRight.equals(getTrue())) {
          return simpleLeft;
        }
        break;
      case OR:
        if (simpleLeft.equals(getTrue())
            || simpleRight.equals(getTrue())
            || simpleLeft.isNegationOf(simpleRight)) {
          return getTrue();
        } else if (simpleLeft.equals(simpleRight)) {
          return simpleLeft;
        } else if (simpleLeft.equals(getFalse())) {
          return simpleRight;
        } else if (simpleRight.equals(getFalse())) {
          return simpleLeft;
        }
        break;
      default:
        // Currently no optimizations for other cases
        // TODO: Add more simplifications
        break;
    }
    return new ACSLLogicalPredicate(simpleLeft, simpleRight, operator);
  }

  @Override
  public boolean equals(Object o) {
    return equalsExceptNegation(o, true);
  }

  @Override
  public int hashCode() {
    int sign = isNegated() ? -1 : 1;
    return sign * (17 * left.hashCode() + 13 * right.hashCode() + operator.hashCode());
  }

  private boolean equalsExceptNegation(Object o, boolean shouldNegationMatch) {
    if (o instanceof ACSLLogicalPredicate) {
      ACSLLogicalPredicate other = (ACSLLogicalPredicate) o;
      if (shouldNegationMatch == (isNegated() == other.isNegated())) {
        return left.equals(other.left)
            && right.equals(other.right)
            && operator.equals(other.operator);
      }
    }
    return false;
  }

  @Override
  public boolean isNegationOf(ACSLPredicate o) {
    return equalsExceptNegation(o, false);
  }

  @Override
  public ExpressionTree<Object> toExpressionTree(ACSLToCExpressionVisitor visitor) {
    ACSLPredicate purePredicate = toPureC();
    if (equals(purePredicate)) {
      ExpressionTree<Object> leftTree;
      ExpressionTree<Object> rightTree;
      switch (operator) {
        case AND:
          if (isNegated()) {
            leftTree = left.negate().toExpressionTree(visitor);
            rightTree = right.negate().toExpressionTree(visitor);
            return Or.of(leftTree, rightTree);
          }
          leftTree = left.toExpressionTree(visitor);
          rightTree = right.toExpressionTree(visitor);
          return And.of(leftTree, rightTree);
        case OR:
          if (isNegated()) {
            leftTree = left.negate().toExpressionTree(visitor);
            rightTree = right.negate().toExpressionTree(visitor);
            return And.of(leftTree, rightTree);
          }
          leftTree = left.toExpressionTree(visitor);
          rightTree = right.toExpressionTree(visitor);
          return Or.of(leftTree, rightTree);
        default:
          throw new AssertionError("Pure predicate should contain AND or OR");
      }
    } else {
      return purePredicate.toExpressionTree(visitor);
    }
  }
}
