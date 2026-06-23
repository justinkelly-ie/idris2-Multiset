module Math.Sing

%default total

||| A singleton coordinate structure representing a single-value state (node).
||| Similar to Math.Pixel but representing a point state rather than a transition.
public export
record Sing (a : Type) where
  constructor MkSing
  val : a

public export
Eq a => Eq (Sing a) where
  (MkSing x) == (MkSing y) = x == y

public export
Show a => Show (Sing a) where
  show (MkSing x) = "[" ++ show x ++ "]"

||| A transition relation between singleton coordinates (source node to target node).
||| This is the logical equivalent of a Pixel (which is a spatial transition relation).
public export
record SingRelation (a : Type) where
  constructor MkSingRelation
  src : Sing a
  tgt : Sing a

public export
Eq a => Eq (SingRelation a) where
  (MkSingRelation s1 t1) == (MkSingRelation s2 t2) = s1 == s2 && t1 == t2

public export
Show a => Show (SingRelation a) where
  show (MkSingRelation s t) = show s ++ " -> " ++ show t

