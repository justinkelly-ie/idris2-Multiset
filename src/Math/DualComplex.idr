module Math.DualComplex

import Math.IntPolynumber
import Math.BoxInt
import Math.Multiset

%default total

||| Dual Complex number a + bε where ε² = 0.
public export
record DualComplex where
  constructor MkDual
  real : BoxInt
  eps  : BoxInt

export
Eq DualComplex where
  (MkDual r1 e1) == (MkDual r2 e2) = (r1 == r2) && (e1 == e2)

export
Show DualComplex where
  show (MkDual r e) = show r ++ " + " ++ show e ++ "ε"

export
addDual : DualComplex -> DualComplex -> DualComplex
addDual (MkDual r1 e1) (MkDual r2 e2) = MkDual (r1 + r2) (e1 + e2)

export
subDual : DualComplex -> DualComplex -> DualComplex
subDual (MkDual r1 e1) (MkDual r2 e2) = MkDual (r1 - r2) (e1 - e2)

export
mulDual : DualComplex -> DualComplex -> DualComplex
mulDual (MkDual r1 e1) (MkDual r2 e2) = MkDual (r1 * r2) (r1 * e2 + r2 * e1)

export
scaleDual : BoxInt -> DualComplex -> DualComplex
scaleDual s (MkDual r e) = MkDual (s * r) (s * e)

||| Convert a DualComplex into an IntPolynumber representation.
export
toIntPoly : DualComplex -> IntPolynumber
toIntPoly (MkDual r e) =
  addMultiset (AddM (0,0) r ZeroM) (AddM (0,1) e ZeroM)

||| Extract DualComplex from an IntPolynumber (truncating powers of ε >= 2).
export
fromIntPoly : IntPolynumber -> DualComplex
fromIntPoly poly =
  let ann = annihilateIntPoly poly
      r = findCoeff (0,0) ann
      e = findCoeff (0,1) ann
  in MkDual r e
  where
    findCoeff : (Nat, Nat) -> IntPolynumber -> BoxInt
    findCoeff _ ZeroM = 0
    findCoeff k (AddM k' v rest) = if k == k' then v else findCoeff k rest
