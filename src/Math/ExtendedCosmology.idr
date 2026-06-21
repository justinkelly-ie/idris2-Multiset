module Math.ExtendedCosmology

import Data.Nat
import Math.BoxInt
import Math.SignedFraction
import Math.Interfaces
import Math.Pixel
import Math.Multiset

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

-----------------------------------------------------------------------
-- UNIVERSAL PROJECTIVE GEOMETRY (Row 10)
--
-- Replaces affine coordinates with homogeneous coordinates [x : y : z]
-- and defines projective cross-ratio invariants.
-----------------------------------------------------------------------
 
||| Homogeneous coordinates [x : y : z] for projective space.
public export
record HomogeneousCoords where
  constructor MkHomogeneous
  x : BoxInt
  y : BoxInt
  z : BoxInt
 
public export
Eq HomogeneousCoords where
  (MkHomogeneous x1 y1 z1) == (MkHomogeneous x2 y2 z2) =
    -- Two homogeneous coordinates are equal if they are proportional:
    -- (x1 * y2 == x2 * y1) and (y1 * z2 == y2 * z1) and (x1 * z2 == x2 * z1)
    (x1 * y2 == x2 * y1) && (y1 * z2 == y2 * z1) && (x1 * z2 == x2 * z1)
 
||| Projective coordinate frame field.
public export
record ProjectiveFrame where
  constructor MkProjFrame
  e1 : HomogeneousCoords
  e2 : HomogeneousCoords
  e3 : HomogeneousCoords
 
||| Computes the projective cross-ratio of four collinear points on a line.
|||
||| (A, B; C, D) = ((C - A) * (D - B)) / ((C - B) * (D - A))
public export
crossRatio : BoxInt -> BoxInt -> BoxInt -> BoxInt -> MSetFraction
crossRatio a b c d =
  let num = (c - a) * (d - b)
      den = (c - b) * (d - a)
      (MkUr denVal) = boxToInt den
  in mkMSF num (Math.Interfaces.integerToNat (abs denVal))
 
||| Perfect point-to-line duality switch (Polar/Wythoff duality).
public export
dualLine : HomogeneousCoords -> (BoxInt, BoxInt, BoxInt)
dualLine (MkHomogeneous x y z) = (x, y, z)
 
-----------------------------------------------------------------------
-- INVERSIVE CHROMOGEOMETRY (Row 12)
--
-- Reflects points through circles/conics rather than lines, mapping
-- bending paths and gravitational horizons.
-----------------------------------------------------------------------
 
||| Relativistic Conic Section coefficients: Ax² + Bxy + Cy² + Dx + Ey + F = 0.
public export
record ConicCoeffs where
  constructor MkConicCoeffs
  a : BoxInt
  b : BoxInt
  c : BoxInt
  d : BoxInt
  e : BoxInt
  f : BoxInt
 
public export
Eq ConicCoeffs where
  (MkConicCoeffs a1 b1 c1 d1 e1 f1) == (MkConicCoeffs a2 b2 c2 d2 e2 f2) =
    a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && e1 == e2 && f1 == f2
 
||| Local helper for Blue quadrance to avoid circular dependency on Math.Chromogeometry
private
localQuadranceBlue : Pixel Blue BoxInt -> Pixel Blue BoxInt -> BoxInt
localQuadranceBlue (MkPixel xA yA) (MkPixel xB yB) =
  let dx = xB - xA
      dy = yB - yA
  in (dx * dx) + (dy * dy)

||| Circle Reflection: reflects a point P through a circle with a given center and quadrance R.
||| In rational geometry: (P' - C) = R / Q(P - C) * (P - C).
||| Returns the reflected coordinates as (MSetFraction, MSetFraction).
public export
circleReflect : Pixel Blue BoxInt -> Pixel Blue BoxInt -> BoxInt -> (MSetFraction, MSetFraction)
circleReflect center pt r =
  let q = localQuadranceBlue center pt
      (MkUr qVal) = boxToInt q
      qNat = Math.Interfaces.integerToNat (abs qVal)
      (MkPixel xc yc) = center
      (MkPixel xp yp) = pt
      dx = xp - xc
      dy = yp - yc
      numX = xc * q + r * dx
      numY = yc * q + r * dy
  in (mkMSF numX qNat, mkMSF numY qNat)
