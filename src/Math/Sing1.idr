module Math.Sing1

%default total

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
