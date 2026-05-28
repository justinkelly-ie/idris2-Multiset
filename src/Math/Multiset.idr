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

