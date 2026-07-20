module Math.Vexel.Vexel

import Math.Multiset
import Math.Singleton.Sing
import Math.Fraction
import Math.SignedFraction
import Math.Singleton.Bit
import Data.List

%default total

||| A Vexel is a one-dimensional state vector represented as a multiset of Singletons.
||| This is Wildberger's discrete, algebraic replacement for a standard vector.
public export
Vexel : (c : Type) -> (a : Type) -> Type
Vexel c a = Multiset c (Sing a)

||| A Fractional Vexel bridges the gap into the middle rows (Row 3+).
||| It tracks 1D arrays of exact rational fractional weights instead of bits.
public export
FractionalVexel : Type
FractionalVexel = Multiset Fraction (Sing Nat)

||| Checks if a singleton is full (non-zero).
||| Since Sing always holds a value, any Sing a is always full.
public export
isFull : Sing a -> Bool
isFull _ = True

||| Check if an item exists in a list (wrapper for elem).
public export
contains : Eq a => a -> List a -> Bool
contains = elem

||| Removes the first occurrence of an item from a list.
public export
removeFirst : Eq a => a -> List a -> List a
removeFirst _ [] = []
removeFirst x (y :: ys) = if x == y then ys else y :: removeFirst x ys

||| Evaluates addition (`+`) across a Vexel container.
||| Governed entirely by the localized structural fold-in rule:
||| Adding two filled singleton tokens inside the same cell forces a collapse.
public export
addVexels : (Eq a, Num c, Eq c) => Vexel c a -> Vexel c a -> Vexel c a
addVexels x y = annihilateMultiset (addMultiset x y)

||| Provides a clean interface to step out of the logic rows and enter the Vexels
||| of Fractions middle layer (original Row 3), converting binary tokens into
||| prime-encoded numbers ([2] / [1]) that can be scaled up arbitrarily.
public export
liftToFractionalVexel : Eq a => Vexel Bit a -> FractionalVexel
liftToFractionalVexel ZeroM = ZeroM
liftToFractionalVexel (AddM (MkSing x) w rest) =
  if isOne w
     then AddM (MkSing 0) (MkFraction 2 1) (liftToFractionalVexel rest)
     else liftToFractionalVexel rest
