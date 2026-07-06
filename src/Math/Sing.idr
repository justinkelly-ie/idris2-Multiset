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

public export
(+) : (Eq a, Eq c, Num c) => Sing c a -> Sing c a -> Sing c a
ZeroS + y = y
x + ZeroS = x
(OneS x1 c1) + (OneS x2 c2) =
  if x1 == x2
    then let sum = c1 + c2 in
         if sum == 0 then ZeroS else OneS x1 sum
    else ZeroS


||| A strictly positive singleton multiset with value 1 = [[]].
||| Restricts the multiset structure to exactly one element.
public export
record Sing1 (c : Type) (a : Type) where
  constructor MkSing1
  val : a
  count : c

public export
(Eq a, Eq c) => Eq (Sing1 c a) where
  (MkSing1 coord1 count1) == (MkSing1 coord2 count2) = coord1 == coord2 && count1 == count2

public export
(Show a, Show c) => Show (Sing1 c a) where
  show (MkSing1 coord count) = "[(" ++ show coord ++ ", " ++ show count ++ ")]"

namespace Sing1Ops
  public export
  (+) : (Eq a, Num c) => Sing1 c a -> Sing1 c a -> Sing1 c a
  (MkSing1 v1 c1) + (MkSing1 v2 c2) =
    if v1 == v2
      then MkSing1 v1 (c1 + c2)
      else MkSing1 v1 c1


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
