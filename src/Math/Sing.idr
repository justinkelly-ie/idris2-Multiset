module Math.Sing

%default total

||| A singleton multiset with possible values 0 = [] or 1 = [[]].
||| Restricts the multiset structure to at most one element.
public export
data Sing : (c : Type) -> (a : Type) -> Type where
  ZeroS : Sing c a
  OneS : a -> c -> Sing c a

public export
(Eq a, Eq c) => Eq (Sing c a) where
  ZeroS == ZeroS = True
  (OneS x1 c1) == (OneS x2 c2) = x1 == x2 && c1 == c2
  _ == _ = False

public export
(Show a, Show c) => Show (Sing c a) where
  show ZeroS = "[]"
  show (OneS x c) = "[(" ++ show x ++ ", " ++ show c ++ ")]"

||| A transition relation between coordinates.
public export
record SingRelation (a : Type) where
  constructor MkSingRelation
  src : a
  tgt : a

public export
Eq a => Eq (SingRelation a) where
  (MkSingRelation s1 t1) == (MkSingRelation s2 t2) = s1 == s2 && t1 == t2

public export
Show a => Show (SingRelation a) where
  show (MkSingRelation s t) = show s ++ " -> " ++ show t
