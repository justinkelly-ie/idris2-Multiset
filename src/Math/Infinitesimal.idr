module Math.Infinitesimal

import Math.IntPolynumber
import Math.DualComplex
import Math.BoxInt
import Math.Multiset

%default total

||| Single-variable PolyNumber (Multiset BoxInt Nat) where key is power of α.
public export
PolyNumber : Type
PolyNumber = Multiset BoxInt Nat

||| Convert a single-variable PolyNumber into a 2D IntPolynumber with β-power 0.
export
toBipoly : PolyNumber -> IntPolynumber
toBipoly ZeroM = ZeroM
toBipoly (AddM n c rest) = AddM (n, 0) c (toBipoly rest)

||| Faulhaber derivative ∂(αⁿ) = n * αⁿ⁻¹ defined purely algebraically on PolyNumber.
export
derivePoly : PolyNumber -> PolyNumber
derivePoly ZeroM = ZeroM
derivePoly (AddM 0 _ rest) = derivePoly rest
derivePoly (AddM n c rest) = AddM (minus n 1) (fromInteger (cast n) * c) (derivePoly rest)

||| Power of BoxInt to a Nat power.
public export
boxPow : BoxInt -> Nat -> BoxInt
boxPow _ 0 = 1
boxPow x (S k) = x * boxPow x k

||| Evaluate a PolyNumber at a BoxInt.
export
evalPoly : PolyNumber -> BoxInt -> BoxInt
evalPoly ZeroM _ = 0
evalPoly (AddM n c rest) x = (c * boxPow x n) + evalPoly rest x

||| Evaluate a PolyNumber at a DualComplex number: P(a + bε) = P(a) + P'(a)*bε.
export
evalDual : PolyNumber -> DualComplex -> DualComplex
evalDual poly (MkDual a b) =
  let pA = evalPoly poly a
      pDerivA = evalPoly (derivePoly poly) a
  in MkDual pA (pDerivA * b)

||| Algebraic multiplication of PolyNumbers.
export
mulPoly : PolyNumber -> PolyNumber -> PolyNumber
mulPoly p1 p2 = annihilateMultiset (mulOuter p1 p2)
  where
    mulInner : Nat -> BoxInt -> PolyNumber -> PolyNumber
    mulInner _ _ ZeroM = ZeroM
    mulInner n1 c1 (AddM n2 c2 rest) = AddM (n1 + n2) (c1 * c2) (mulInner n1 c1 rest)

    mulOuter : PolyNumber -> PolyNumber -> PolyNumber
    mulOuter ZeroM _ = ZeroM
    mulOuter (AddM n c rest) ys = addMultiset (mulInner n c ys) (mulOuter rest ys)
