module Math.OnSeq.OnMSet

import Math.Multiset
import Math.Pixel
import Math.Maxel
import Math.Vexel
import Math.Sing
import Math.Fraction

%default total

||| An on-sequence (ongoing sequence) starting at a specific index.
||| Defined via a generator function mapping the term index to the value.
public export
record OnSeq a where
  constructor MkOnSeq
  start : Nat
  at    : Nat -> a

||| A finite consecutive subsequence (clip) extracted from a sequence.
public export
record Clip a where
  constructor MkClip
  startIdx : Nat
  elements : List a

export
(Show a) => Show (Clip a) where
  show (MkClip idx elems) = "Clip@" ++ show idx ++ show elems ++ "..."

||| Creates a constant on-sequence starting at a specific index.
public export
constant : Nat -> a -> OnSeq a
constant s x = MkOnSeq s (\_ => x)

||| Creates the identity on-sequence [n> starting at a specific index (usually 0 or 1).
public export
identity : Nat -> OnSeq Nat
identity s = MkOnSeq s (\n => n)

||| Evaluates/indexes the on-sequence at a specific term index.
||| Returns `Just value` if index >= start, else `Nothing`.
public export
getTerm : OnSeq a -> Nat -> Maybe a
getTerm (MkOnSeq start at) n =
  if n >= start
     then Just (at n)
     else Nothing

||| Extracts a finite clip of a given length starting from the specified index.
||| Returns a Clip starting at max(idx, start).
public export
getClip : OnSeq a -> (idx : Nat) -> (len : Nat) -> Clip a
getClip (MkOnSeq start at) idx len =
  let actualStart = max idx start
  in MkClip actualStart (generateElements actualStart len)
  where
    generateElements : Nat -> Nat -> List a
    generateElements _ Z = []
    generateElements curr (S k) = at curr :: generateElements (S curr) k

||| Maps a function over an on-sequence.
public export
map : (a -> b) -> OnSeq a -> OnSeq b
map f (MkOnSeq start at) = MkOnSeq start (\n => f (at n))

||| Combines two on-sequences pointwise.
||| The resulting on-sequence starts at the maximum of the two starting indices.
public export
zipWith : (a -> b -> c) -> OnSeq a -> OnSeq b -> OnSeq c
zipWith f (MkOnSeq s1 at1) (MkOnSeq s2 at2) =
  let newStart = max s1 s2
  in MkOnSeq newStart (\n => f (at1 n) (at2 n))

-----------------------------------------------------------------------
-- SPECIALIZED ON-SEQUENCES FOR THE MULTISET MATH SUITE
-----------------------------------------------------------------------

||| On-sequence of multisets.
public export
0 OnMSet : (c : Type) -> (a : Type) -> Type
OnMSet c a = OnSeq (Multiset c a)

||| Pointwise addition of two on-sequences of multisets.
public export
addOnMSet : (OnMSet c a) -> (OnMSet c a) -> (OnMSet c a)
addOnMSet = zipWith addMultiset

||| Maps multiset annihilation over an on-sequence of multisets.
public export
annihilateOnMSet : (Eq a, Num c, Eq c) => OnMSet c a -> OnMSet c a
annihilateOnMSet = map annihilateMultiset

||| Maps scalar scaling over an on-sequence of multisets.
public export
scaleOnMSet : (Num c, Eq c) => c -> OnMSet c a -> OnMSet c a
scaleOnMSet scalar = map (scaleMultiset scalar)

||| Swaps matter and antimatter across the on-sequence.
public export
negateOnMSet : Neg c => OnMSet c a -> OnMSet c a
negateOnMSet = map negateMultiset

||| Pointwise subtraction of two on-sequences of multisets.
public export
subOnMSet : Neg c => OnMSet c a -> OnMSet c a -> OnMSet c a
subOnMSet = zipWith subMultiset

||| On-sequence of Maxels (transition relations).
public export
0 OnMaxel : (metric : Metric) -> (c : Type) -> (a : Type) -> Type
OnMaxel metric c a = OnSeq (Maxel metric c a)

||| Pointwise addition of two on-sequences of Maxels.
public export
addOnMaxel : OnMaxel metric c a -> OnMaxel metric c a -> OnMaxel metric c a
addOnMaxel = zipWith addMultiset

||| Supports transition mapping of an on-sequence containing Maybe Pixels.
public export
supportOnMaxel : (Eq a, Num c, Eq c) => OnSeq (Multiset c (Maybe (Pixel metric a))) -> OnMaxel metric c a
supportOnMaxel = map supportMaxel

||| On-sequence of Vexels.
public export
0 OnVexel : (c : Type) -> (a : Type) -> Type
OnVexel c a = OnSeq (Vexel c a)

||| Pointwise addition of two on-sequences of Vexels.
public export
addOnVexel : (Eq c, Eq a) => OnVexel c a -> OnVexel c a -> OnVexel c a
addOnVexel = zipWith addVexels

||| Lifts an on-sequence of binary singleton Vexels to fractional rational Vexels.
public export
liftOnVexel : OnVexel c a -> OnSeq FractionalVexel
liftOnVexel = map liftToFractionalVexel

||| On-sequence of singletons.
public export
0 OnSing : (c : Type) -> (a : Type) -> Type
OnSing c a = OnSeq (Sing c a)

||| Pointwise addition of two on-sequences of singletons.
public export
addOnSing : (Eq a, Eq c, Num c) => OnSing c a -> OnSing c a -> OnSing c a
addOnSing = zipWith (+)


||| Lookup the multiplicity count of an element in a multiset.
public export
lookupCount : (Eq a, Num c) => a -> Multiset c a -> c
lookupCount _ ZeroM = 0
lookupCount k (AddM x c xs) =
  if k == x
     then c + lookupCount k xs
     else lookupCount k xs

||| Computes the Möbius Maxel from a Zeta Maxel for a finite set of sorted nodes.
||| Zeta relation has count 1 for i <= j.
||| Returns the Möbius Maxel containing pixels with their correct Mobius counts.
public export
mobiusFromZeta : (Eq a, Num c, Neg c, Eq c) 
               => List a 
               -> Maxel metric c a 
               -> Maxel metric c a
mobiusFromZeta nodes zeta =
  let fuel = length nodes
  in fromList (concatMap (\i => map (\j => (MkPixel i j, mu fuel i j)) nodes) nodes)
  where
    zetaVal : a -> a -> c
    zetaVal u v = lookupCount (MkPixel u v) zeta

    mu : Nat -> a -> a -> c
    mu Z _ _ = 0
    mu (S f) i j =
      if i == j
         then 1
         else if zetaVal i j == 0
                 then 0
                 else negate (sumOver i j nodes)
      where
        sumOver : a -> a -> List a -> c
        sumOver _ _ [] = 0
        sumOver u v (k :: rest) =
          if u == k
             then sumOver u v rest
             else let term = if zetaVal u k /= 0 then zetaVal u k * mu f k v else 0
                  in term + sumOver u v rest

