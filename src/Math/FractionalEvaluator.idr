module Math.FractionalEvaluator

import Math.Fraction
import Math.IntPolynumber
import Math.BoxInt
import Math.Interfaces

%default total

||| Evaluates an IntPolynumber (a Multiset of (alpha, beta)) given a fractional `s` for alpha.
||| We assume beta is always 0 (as is standard for SpreadPolynomials).
public export
evaluateIntPoly : IntPolynumber -> Spread -> Spread
evaluateIntPoly poly spread =
  let (posSum, negSum) = evalHelper poly
  in MkSpread (subFraction posSum negSum)
  where
    evalHelper : IntPolynumber -> (Fraction, Fraction)
    evalHelper ZeroM = (MkFraction 0 1, MkFraction 0 1)
    evalHelper (AddM (alphaPower, _) coeff rest) =
      let (posAcc, negAcc) = evalHelper rest
          powered = powerFraction spread.value alphaPower
          (MkUr coeffVal) = boxToInt coeff
          mag = Prelude.integerToNat (abs coeffVal)
          scaled = scaleFraction mag powered
      in if coeffVal >= 0 
           then (addFraction posAcc scaled, negAcc)
           else (posAcc, addFraction negAcc scaled)
