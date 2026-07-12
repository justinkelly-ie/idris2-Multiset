module Math.Singleton.Sing

import Math.Multiset

%default total

-----------------------------------------------------------------------
-- SING
--
-- A singleton multiset: a multiset containing exactly one element,
-- where that element is itself a Multiset.
--
-- Concretely, Sing c a = { m : Multiset c a }.
-- The single element is a Multiset c a value; Sing wraps it.
-----------------------------------------------------------------------

||| A singleton multiset holding exactly one element, which is itself a Multiset.
||| `Sing c a` represents { m } where m : Multiset c a.
public export
record Sing (c : Type) (a : Type) where
  constructor MkSing
  element : Multiset c a

public export
(Eq a, Eq c, Neg c, Num c) => Eq (Sing c a) where
  (MkSing m1) == (MkSing m2) = m1 == m2

public export
(Show a, Show c) => Show (Sing c a) where
  show (MkSing m) = "[" ++ show m ++ "]"

-----------------------------------------------------------------------
-- SING OPERATIONS
-----------------------------------------------------------------------

||| The singleton containing the empty multiset: { [] }.
public export
emptySing : Sing c a
emptySing = MkSing ZeroM

||| Embed a Multiset as a Sing.
public export
toSing : Multiset c a -> Sing c a
toSing m = MkSing m

||| Extract the contained Multiset from a Sing.
public export
fromSing : Sing c a -> Multiset c a
fromSing (MkSing m) = m

-----------------------------------------------------------------------
-- TRANSITION RELATION
--
-- Preserved from the original: a relation between two coordinates.
-----------------------------------------------------------------------

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
