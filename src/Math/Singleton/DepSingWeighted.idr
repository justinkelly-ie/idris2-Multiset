module Math.Singleton.DepSingWeighted

import Math.Singleton.DepSing

%default total

||| A dependently typed weighted singleton primitive.
||| Tracks coordinate element `x` and weight `weight` at the type level.
public export
data DepSingWeighted : (c : Type) -> (a : Type) -> a -> c -> Type where
  MkDepSingWeighted : (x : a) -> (weight : c) -> DepSingWeighted c a x weight

||| A dependent singleton type synonym.
public export
0 Sing : (c : Type) -> (a : Type) -> a -> c -> Type
Sing c a x weight = DepSingWeighted c a x weight

||| A dependent singleton where the weight is non-zero.
public export
0 Sing1 : (c : Type) -> (Eq c, Num c) => (a : Type) -> a -> c -> Type
Sing1 c a x weight = (Sing c a x weight, (weight == 0) = False)
