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
