module Math.Multiset

import Data.List
import Data.Linear
import Math.Interfaces
import public Math.Pixel

%default covering

||| A Run-Length Encoded (RLE) Multiset optimized for high-generation Box Arithmetic.
||| Instead of storing N identical elements structurally, it stores the element and an Integer count.
||| Positive count represents pos (Matter), negative count represents neg (Antimatter).
|||


public export
data Multiset : Type -> Type where
  ZeroM : Multiset a
  AddM : a -> Integer -> Multiset a -> Multiset a

||| Strictly positive, non-empty Multiset (guarantees at least one element)
||| Used to prevent division-by-zero in fractional spreads.
public export
data Multiset1 : Type -> Type where
  BaseM : a -> Integer -> Multiset1 a
  AddM1 : a -> Integer -> Multiset1 a -> Multiset1 a

public export
insertItem : Eq a => a -> Integer -> Multiset a -> Multiset a
insertItem k v ZeroM = AddM k v ZeroM
insertItem k v (AddM k' v' rest) =
  if k == k' then
    let newV = v + v'
    in if newV == 0 then rest else AddM k newV rest
  else AddM k' v' (insertItem k v rest)

||| Addition on Multiset is Lazy (Deferred).
||| Instead of eagerly scanning for annihilations, it simply concatenates the RLE vectors.
||| This drops the complexity from O(N*M) to O(N).
public export
addMultiset : Multiset a -> Multiset a -> Multiset a
addMultiset ZeroM ys = ys
addMultiset (AddM x c xs) ys = AddM x c (addMultiset xs ys)

||| Explicitly computes the annihilation for a Multiset by merging duplicates.
||| Should be called at the end of an Epoch to compress the state vector.
public export
annihilateMultiset : Eq a => Multiset a -> Multiset a
annihilateMultiset xs = go ZeroM xs
  where
    go : Multiset a -> Multiset a -> Multiset a
    go acc ZeroM = acc
    go acc (AddM k v rest) = go (insertItem k v acc) rest

||| Computes the total multiplicity (total Leibniz Lag) of the Multiset.
public export
multiplicityAll : Multiset a -> Integer
multiplicityAll ZeroM = 0
multiplicityAll (AddM x c xs) = abs c + multiplicityAll xs

||| Scalar multiplication: multiplies the multiplicities.
public export
scaleMultiset : Integer -> Multiset a -> Multiset a
scaleMultiset scalar xs = if scalar == 0 then ZeroM else go xs
  where
    go : Multiset a -> Multiset a
    go ZeroM = ZeroM
    go (AddM k v rest) = AddM k (v * scalar) (go rest)

||| Negation swaps matter and antimatter
public export
negateMultiset : Multiset a -> Multiset a
negateMultiset ZeroM = ZeroM
negateMultiset (AddM x c xs) = AddM x (-c) (negateMultiset xs)

||| Subtraction (Lazy)
public export
subMultiset : Multiset a -> Multiset a -> Multiset a
subMultiset a b = addMultiset a (negateMultiset b)



export
Eq a => Eq (Multiset a) where
  a == b = 
    let res = annihilateMultiset (addMultiset a (negateMultiset b))
    in isEmpty res
    where
      isEmpty : {0 b : Type} -> Multiset b -> Bool
      isEmpty ZeroM = True
      isEmpty _ = False

export
Show a => Show (Multiset a) where
  show ZeroM = "[]"
  show xs = "[" ++ showItems xs ++ "]"
    where
      showItems : Multiset a -> String
      showItems ZeroM = ""
      showItems (AddM k v ZeroM) = "(" ++ show k ++ ", " ++ show v ++ ")"
      showItems (AddM k v rest) = "(" ++ show k ++ ", " ++ show v ++ "), " ++ showItems rest

public export
multisetToList : Multiset a -> List (a, Integer)
multisetToList ZeroM = []
multisetToList (AddM k v rest) = (k, v) :: multisetToList rest

public export
fromList : Eq a => List (a, Integer) -> Multiset a
fromList [] = ZeroM
fromList ((k, v) :: rest) = insertItem k v (fromList rest)

-----------------------------------------------------------------------
-- MAXEL & BOX ARITHMETIC MULTIPLICATION (Dynamic Annihilation Policies)
-----------------------------------------------------------------------

||| A Maxel is a Multiset of Pixels, representing transition relations.
public export
0 Maxel : Type -> Type
Maxel a = Multiset (Pixel a)

||| Dynamic Maxel multiplication (Transitive Product).
||| Multiplies two Maxels element-wise. The product of [a,b] and [c,d] is Just [a,d] if b == c, and Nothing otherwise.
||| The result is a multiset of Maybe (Pixel a) entries, tracking unsuccessful annihilations as Nothing.
public export
mulMaxel : Eq a => Maxel a -> Maxel a -> Multiset (Maybe (Pixel a))
mulMaxel ZeroM _ = ZeroM
mulMaxel (AddM p1 c1 rest) m2 =
  addMultiset (mulInner p1 c1 m2) (mulMaxel rest m2)
  where
    mulInner : Pixel a -> Integer -> Maxel a -> Multiset (Maybe (Pixel a))
    mulInner _ _ ZeroM = ZeroM
    mulInner px cx (AddM py cy ys) =
      let pProd = mulPixel px py
          prodCount = cx * cy
      in insertItem pProd prodCount (mulInner px cx ys)

||| Takes the support of a multiplied Maxel.
||| Filters out all 'Nothing' entries (representing annihilated or non-transitive transitions),
||| returning a clean Maxel containing only the valid remaining transitions.
public export
supportMaxel : Eq a => Multiset (Maybe (Pixel a)) -> Maxel a
supportMaxel ZeroM = ZeroM
supportMaxel (AddM Nothing c rest) = supportMaxel rest
supportMaxel (AddM (Just px) c rest) = AddM px c (supportMaxel rest)

-----------------------------------------------------------------------
-- LINEAR DEPENDENT MULTISET (Type-Verified Algebraic Invariant)
-----------------------------------------------------------------------

||| A strictly linear dependent signed multiset.
||| The exact elements and their integer multiplicities are tracked in the type signature.
||| The `1` multiplicity guarantees un-forgeable physical conservation and enables O(1) in-place mutation.
public export
data LMultiset : (a : Type) -> (contents : List (a, Integer)) -> Type where
  ||| The vacuum state.
  LEmptyM : LMultiset a []
  
  ||| Adds an element, strictly consuming the previous state linearly.
  LAddM : {0 rest : List (a, Integer)} ->
          (item : a) -> 
          (count : Integer) -> 
          (1 prev : LMultiset a rest) -> 
          LMultiset a ((item, count) :: rest)

||| Legacy compatibility alias for LMultiset.
public export
0 LDepMultiset : (a : Type) -> (contents : List (a, Integer)) -> Type
LDepMultiset = LMultiset


