module Math.Singleton.Sing

%default total

-----------------------------------------------------------------------
-- SING
--
-- A singleton: a transparent wrapper for exactly one element of type `a`.
--
-- Unlike Maybe or the old ZeroS/OneS form, Sing always holds an element.
-- It encodes WHICH value is present, not WHETHER a value is present.
--
-- The element type `a` determines the domain; Sing adds no restriction.
-- B₂ restriction (to { ZeroM, [[]] }) is enforced at the Bit level.
-----------------------------------------------------------------------

||| A singleton holding exactly one element of type `a`.
public export
data Sing : (a : Type) -> Type where
  MkSing : a -> Sing a

public export
Eq a => Eq (Sing a) where
  (MkSing x) == (MkSing y) = x == y

public export
Show a => Show (Sing a) where
  show (MkSing x) = "{" ++ show x ++ "}"

-----------------------------------------------------------------------
-- SING OPERATIONS
-----------------------------------------------------------------------

||| Wrap a value in a singleton.
public export
toSing : a -> Sing a
toSing = MkSing

||| Extract the element from a singleton.
public export
fromSing : Sing a -> a
fromSing (MkSing x) = x

-----------------------------------------------------------------------
-- SING1
--
-- A strictly-present singleton: exactly one element.
-- Preserved as an alias for Sing — Sing is always strictly present.
-----------------------------------------------------------------------

||| A guaranteed-present singleton. Alias for Sing.
public export
Sing1 : Type -> Type
Sing1 = Sing

-----------------------------------------------------------------------
-- TRANSITION RELATION
-----------------------------------------------------------------------

||| A transition relation between two coordinates.
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
