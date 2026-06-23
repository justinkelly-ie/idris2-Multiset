module Math.Sing1

import Math.Sing

%default total

||| A strictly positive singleton multiset (exactly 1 element, count is non-zero).
||| Guarantees division-by-zero protection at the type level.
public export
record Sing1 (c : Type) (a : Type) where
  constructor MkSing1
  coord : Sing a
  count : c

public export
(Eq a, Eq c) => Eq (Sing1 c a) where
  (MkSing1 coord1 count1) == (MkSing1 coord2 count2) = coord1 == coord2 && count1 == count2

public export
(Show a, Show c) => Show (Sing1 c a) where
  show (MkSing1 coord count) = show coord ++ " * " ++ show count
