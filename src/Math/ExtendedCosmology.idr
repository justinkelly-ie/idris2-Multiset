module Math.ExtendedCosmology

import Data.Nat

||| Core nested power structures (1, 2, 3...) with no zero base case.
public export
data PositivePower : Type where
  One  : PositivePower
  Nest : PositivePower -> PositivePower

public export
Eq PositivePower where
  One == One = True
  (Nest x) == (Nest y) = x == y
  _ == _ = False

||| Matter vs. Antimatter following Wildberger's signed multiset rules.
||| Banishment of the zero/annihilated case at this layer.
public export
data SignedMatter : Type where
  Matter     : PositivePower -> SignedMatter  -- Positive Multiset
  Antimatter : PositivePower -> SignedMatter  -- Negative Multiset

public export
Eq SignedMatter where
  (Matter x) == (Matter y) = x == y
  (Antimatter x) == (Antimatter y) = x == y
  _ == _ = False

||| Tropical Semiring structure tracking background space expansion (Dark Energy).
public export
record DarkEnergyMetric where
  constructor Expansion
  scale : Nat

public export
Eq DarkEnergyMetric where
  (Expansion a) == (Expansion b) = a == b

public export
tropicalAdd : DarkEnergyMetric -> DarkEnergyMetric -> DarkEnergyMetric
tropicalAdd (Expansion a) (Expansion b) = Expansion (max a b)

public export
tropicalMultiply : DarkEnergyMetric -> DarkEnergyMetric -> DarkEnergyMetric
tropicalMultiply (Expansion a) (Expansion b) = Expansion (a + b)

||| Helper to convert a Nat into our nested PositivePower type.
public export
toPositivePowerNat : Nat -> PositivePower
toPositivePowerNat Z = One
toPositivePowerNat (S k) = Nest (toPositivePowerNat k)

||| Helper to convert a positive Integer into our nested PositivePower type.
public export
toPositivePower : Integer -> PositivePower
toPositivePower n = toPositivePowerNat (cast (if n <= 1 then 0 else n - 1))

||| Converts a standard Integer to non-zero signed matter.
public export
toSignedMatter : Integer -> SignedMatter
toSignedMatter n = 
  if n > 0 
     then Matter (toPositivePower n)
     else if n < 0 
             then Antimatter (toPositivePower (abs n))
             else Matter One -- 0 defaults to active vacuum fluctuation

