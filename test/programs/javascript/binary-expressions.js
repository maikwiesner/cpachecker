function __VERIFIER_error() {}

// TODO use global object definition of NaN and Number.isNaN when it is implemented
var NaN = -(-undefined);
function isNaN(value) {
  return value !== value;
}
if (!isNaN(NaN)) { __VERIFIER_error(); }
if (isNaN(0)) { __VERIFIER_error(); }

// strict (un-) equality
if (2 === 3) { __VERIFIER_error(); }
if (3 !== 3) { __VERIFIER_error(); }
if (3 !== 3.0) { __VERIFIER_error(); }
if (3 !== 3.0) { __VERIFIER_error(); }

// binary operators
if (1 + 2 !== 3) { __VERIFIER_error(); }
if (3 + 2 === 3) { __VERIFIER_error(); }
if (5 - 2 !== 3) { __VERIFIER_error(); }
if (5 - 3 === 3) { __VERIFIER_error(); }

// -------------------------------------------------------------------------------
// multiplication, see https://www.ecma-international.org/ecma-262/5.1/#sec-11.5.1
// -------------------------------------------------------------------------------
// If either operand is NaN, the result is NaN.
if (!isNaN(NaN * 3)) { __VERIFIER_error(); }
if (!isNaN(3 * NaN)) { __VERIFIER_error(); }
// The sign of the result is positive if both operands have the same sign,
// negative if the operands have different signs.
if ( 2 *  3 !==  6) { __VERIFIER_error(); }
if (-2 * -3 !==  6) { __VERIFIER_error(); }
if ( 2 * -3 !== -6) { __VERIFIER_error(); }
if (-2 *  3 !== -6) { __VERIFIER_error(); }
// Multiplication of an infinity by a zero results in NaN.
if (!isNaN( Infinity * 0)) { __VERIFIER_error(); }
if (!isNaN(-Infinity * 0)) { __VERIFIER_error(); }
if (!isNaN(0 *  Infinity)) { __VERIFIER_error(); }
if (!isNaN(0 * -Infinity)) { __VERIFIER_error(); }
// Multiplication of an infinity by an infinity results in an infinity.
// The sign is determined by the rule already stated above.
if ( Infinity *  Infinity !==  Infinity) { __VERIFIER_error(); }
if (-Infinity * -Infinity !==  Infinity) { __VERIFIER_error(); }
if (-Infinity *  Infinity !== -Infinity) { __VERIFIER_error(); }
if ( Infinity * -Infinity !== -Infinity) { __VERIFIER_error(); }
// Multiplication of an infinity by a finite nonzero value results in a signed infinity.
// The sign is determined by the rule already stated above.
if ( Infinity *  9 !==  Infinity) { __VERIFIER_error(); }
if (-Infinity * -9 !==  Infinity) { __VERIFIER_error(); }
if (-Infinity *  9 !== -Infinity) { __VERIFIER_error(); }
if ( Infinity * -9 !== -Infinity) { __VERIFIER_error(); }
if ( 9 *  Infinity !==  Infinity) { __VERIFIER_error(); }
if (-9 * -Infinity !==  Infinity) { __VERIFIER_error(); }
if ( 9 * -Infinity !== -Infinity) { __VERIFIER_error(); }
if (-9 *  Infinity !== -Infinity) { __VERIFIER_error(); }
// In the remaining cases, where neither an infinity or NaN is involved,
// the product is computed and rounded to the nearest representable value using
// IEEE 754 round-to-nearest mode.
// If the magnitude is too large to represent,
// the result is then an infinity of appropriate sign.
// If the magnitude is too small to represent,
// the result is then a zero of appropriate sign.
// The ECMAScript language requires support of gradual underflow as defined by IEEE 754.
// TODO test edge cases described in comment above
if (0 * 3 !== 0) { __VERIFIER_error(); }
if (2 * 3 !== 6) { __VERIFIER_error(); }
if (-2 * 3 !== -6) { __VERIFIER_error(); }
if (-2 * -3 !== 6) { __VERIFIER_error(); }
if (0.2 * 0.5 !== 0.1) { __VERIFIER_error(); }

// -------------------------------------------------------------------------------
// division, see https://www.ecma-international.org/ecma-262/5.1/#sec-11.5.2
// -------------------------------------------------------------------------------
// If either operand is NaN, the result is NaN.
if (!isNaN(NaN / 3)) { __VERIFIER_error(); }
if (!isNaN(3 / NaN)) { __VERIFIER_error(); }
// The sign of the result is positive if both operands have the same sign, negative if the operands
// have different signs.
if ( 6 /  3 !==  2) { __VERIFIER_error(); }
if (-6 / -3 !==  2) { __VERIFIER_error(); }
if ( 6 / -3 !== -2) { __VERIFIER_error(); }
if (-6 /  3 !== -2) { __VERIFIER_error(); }

if (Infinity !== (9999999 / 0)) { __VERIFIER_error(); }
// Division of an infinity by an infinity results in NaN.
if (!isNaN(Infinity / Infinity)) { __VERIFIER_error(); }
if (!isNaN(Infinity / -Infinity)) { __VERIFIER_error(); }
if (!isNaN(-Infinity / Infinity)) { __VERIFIER_error(); }
if (!isNaN(-Infinity / -Infinity)) { __VERIFIER_error(); }
// Division of an infinity by a zero results in an infinity.
// The sign is determined by the rule already stated above.
if (Infinity / 0 !== Infinity) { __VERIFIER_error(); }
if (-Infinity / -0 !== Infinity) { __VERIFIER_error(); }
if (-Infinity / 0 !== -Infinity) { __VERIFIER_error(); }
if (Infinity / -0 !== -Infinity) { __VERIFIER_error(); }
// Division of an infinity by a nonzero finite value results in a signed infinity.
// The sign is determined by the rule already stated above.
if (Infinity / 9 !== Infinity) { __VERIFIER_error(); }
if (-Infinity / -9 !== Infinity) { __VERIFIER_error(); }
if (-Infinity / 9 !== -Infinity) { __VERIFIER_error(); }
if (Infinity / -9 !== -Infinity) { __VERIFIER_error(); }
// Division of a finite value by an infinity results in zero.
// The sign is determined by the rule already stated above.
if (9 / Infinity !== 0) { __VERIFIER_error(); }
if (-9 / -Infinity !== 0) { __VERIFIER_error(); }
if (9 / -Infinity !== -0) { __VERIFIER_error(); }
if (-9 / Infinity !== -0) { __VERIFIER_error(); }
// Division of a zero by a zero results in NaN
if (!isNaN( 0 /  0)) { __VERIFIER_error(); }
if (!isNaN( 0 / -0)) { __VERIFIER_error(); }
if (!isNaN(-0 /  0)) { __VERIFIER_error(); }
if (!isNaN(-0 / -0)) { __VERIFIER_error(); }
// division of zero by any other finite value results in zero, with the sign determined by the
// rule already stated above.
if ( 0 /  9 !==  0) { __VERIFIER_error(); }
if (-0 / -9 !==  0) { __VERIFIER_error(); }
if ( 0 / -9 !== -0) { __VERIFIER_error(); }
if (-0 /  9 !== -0) { __VERIFIER_error(); }
// Division of a nonzero finite value by a zero results in a signed infinity.
// The sign is determined by the rule already stated above.
if (9 / 0 !== Infinity) { __VERIFIER_error(); }
if (-9 / -0 !== Infinity) { __VERIFIER_error(); }
if ( 9 / -0 !== -Infinity) { __VERIFIER_error(); }
if (-9 /  0 !== -Infinity) { __VERIFIER_error(); }
