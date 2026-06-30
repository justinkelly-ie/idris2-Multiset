module Math.DepMaxel

import Math.DepMultiset
import public Math.Pixel

%default covering

||| A dependently typed Maxel is a DepMultiset of Pixels.
public export
0 DepMaxel : (metric : Metric) -> (c : Type) -> (a : Type) -> (contents : List (Pixel metric a, c)) -> Type
DepMaxel metric c a contents = DepMultiset c (Pixel metric a) contents
