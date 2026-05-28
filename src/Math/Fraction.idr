module Math.Fraction

import Data.Nat

%default total

||| A pure algebraic fraction for Rational Trigonometry and exact math.
public export
record Fraction where
  constructor MkFraction
  numerator   : Nat
  denominator : Nat

||| A fraction semantically representing a Spread (sin^2 theta).
public export
record Spread where
  constructor MkSpread
  value : Fraction

||| A fraction semantically representing a Quadrance (distance squared).
public export
record Quadrance where
  constructor MkQuadrance
  value : Fraction

||| Multiplies two fractions exactly.
public export
mulFraction : Fraction -> Fraction -> Fraction
mulFraction f1 f2 = 
  MkFraction (f1.numerator * f2.numerator) (f1.denominator * f2.denominator)

||| A safe recursive natural division that returns 0 if dividing by zero.
||| NOTE: This may need to be revised in the future. Idris 2's zero linearity 
||| (e.g., `0` multiplicity) on the type definition of the empty UnaryMultiset could 
||| potentially be leveraged to structurally forbid zero denominators natively,
||| making this explicit zero-catching logic obsolete.
public export
fractionDivNat : Nat -> Nat -> Nat
fractionDivNat _ Z = Z
fractionDivNat n d = 
  case isLTE d n of
       Yes _ => S (fractionDivNat (assert_smaller n (n `minus` d)) d)
       No  _ => Z

||| Multiplies a fraction by an integer coefficient (represented as Nat for magnitude).
public export
scaleFraction : Nat -> Fraction -> Fraction
scaleFraction scalar f =
  MkFraction (scalar * f.numerator) f.denominator

||| Adds two fractions exactly by finding a common denominator.
public export
addFraction : Fraction -> Fraction -> Fraction
addFraction f1 f2 = 
  let num1 = f1.numerator * f2.denominator
      num2 = f2.numerator * f1.denominator
      den  = f1.denominator * f2.denominator
  in MkFraction (num1 + num2) den

||| Subtracts f2 from f1 exactly (assumes f1 >= f2, bottoms out at 0 if f1 < f2).
public export
subFraction : Fraction -> Fraction -> Fraction
subFraction f1 f2 = 
  let num1 = f1.numerator * f2.denominator
      num2 = f2.numerator * f1.denominator
      den  = f1.denominator * f2.denominator
  in MkFraction (num1 `minus` num2) den

||| Raises a fraction to a natural power.
public export
powerFraction : Fraction -> Nat -> Fraction
powerFraction f Z = MkFraction 1 1
powerFraction f (S k) = mulFraction f (powerFraction f k)
