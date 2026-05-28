module Math.FractionalEvaluator

import Math.Fraction
import Math.IntPolynumber

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
          mag = cast {to=Nat} (abs coeff)
          scaled = scaleFraction mag powered
      in if coeff >= 0 
           then (addFraction posAcc scaled, negAcc)
           else (posAcc, addFraction negAcc scaled)

