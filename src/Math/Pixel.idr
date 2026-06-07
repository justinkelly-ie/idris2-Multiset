module Math.Pixel

||| The core fundamental data structure of the non-linear physics engine.
||| A 2-component coordinate representing a source and target (e.g. x and y).
public export
record Pixel (a : Type) where
  constructor MkPixel
  src : a
  tgt : a

public export
Eq a => Eq (Pixel a) where
  (MkPixel s1 t1) == (MkPixel s2 t2) = s1 == s2 && t1 == t2

public export
Show a => Show (Pixel a) where
  show (MkPixel s t) = "(" ++ show s ++ ", " ++ show t ++ ")"

||| Pixel multiplication in Wildberger's Box Arithmetic.
||| Iff b == c in [a,b] * [c,d] then the product is [a,d]
||| Otherwise, the product is Nothing.
public export
mulPixel : Eq a => Pixel a -> Pixel a -> Maybe (Pixel a)
mulPixel (MkPixel a b) (MkPixel c d) =
  if b == c then Just (MkPixel a d) else Nothing
