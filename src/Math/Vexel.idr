module Math.Vexel

import Math.Multiset
import Math.Sing
import Math.Sing1
import Math.Fraction
import Math.SignedFraction
import Data.List

%default total

||| A Vexel is a one-dimensional state vector represented as a list of singletons.
||| This is Wildberger's discrete, algebraic replacement for a standard vector.
public export
0 Vexel : (c : Type) -> (a : Type) -> Type
Vexel c a = List (Sing c a)

||| A Fractional Vexel bridges the gap into the middle rows (Row 3+).
||| It tracks 1D arrays of exact rational fractional weights instead of bits.
public export
0 FractionalVexel : Type
FractionalVexel = List Fraction

||| Checks if a singleton is full (non-zero).
public export
isFull : Sing c a -> Bool
isFull ZeroS = False
isFull (OneS _ _) = True

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
||| Adding two filled singleton tokens `[[]]` inside the same cell forces a modulo-2 collapse.
public export
addVexels : (Eq c, Eq a) => Vexel c a -> Vexel c a -> Vexel c a
addVexels [] y = y
addVexels x [] = x
addVexels (token :: xs) ys = 
  -- Check if the incoming singleton token already exists in the destination vexel
  if contains token ys 
    then -- Parity Collision: They annihilate each other into the empty multiset `[]`
         addVexels xs (removeFirst token ys)
    else -- Identity: No duplicate token found, insert safely into the array
         token :: addVexels xs ys

||| Provides a clean interface to step out of the logic rows and enter the Vexels
||| of Fractions middle layer (original Row 3), converting binary tokens into
||| prime-encoded numbers ([2] / [1]) that can be scaled up arbitrarily.
public export
liftToFractionalVexel : Vexel c a -> FractionalVexel
liftToFractionalVexel [] = []
liftToFractionalVexel (singToken :: xs) = 
  let liftedFraction = if isFull singToken 
                         then MkFraction 2 1 -- Maps `[[]]` token to prime base ratio 2/1
                         else MkFraction 0 1  -- Maps `[]` token to 0/1
  in liftedFraction :: liftToFractionalVexel xs
