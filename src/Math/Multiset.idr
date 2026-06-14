module Math.Multiset

import Data.List
import Data.Linear
import Math.Interfaces
import public Math.Pixel

%default covering

||| A Run-Length Encoded (RLE) Multiset optimized for high-generation Box Arithmetic.
||| Instead of storing N identical elements structurally, it stores the element and a count.
||| The count type c can be parameterized (e.g. Integer, BoxInt, or Nat).
|||

public export
data Multiset : (c : Type) -> (a : Type) -> Type where
  ZeroM : Multiset c a
  AddM : a -> c -> Multiset c a -> Multiset c a

||| Strictly positive, non-empty Multiset (guarantees at least one element)
||| Used to prevent division-by-zero in fractional spreads.
public export
data Multiset1 : (c : Type) -> (a : Type) -> Type where
  BaseM : a -> c -> Multiset1 c a
  AddM1 : a -> c -> Multiset1 c a -> Multiset1 c a

public export
insertItem : (Eq a, Num c, Eq c) => a -> c -> Multiset c a -> Multiset c a
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
addMultiset : Multiset c a -> Multiset c a -> Multiset c a
addMultiset ZeroM ys = ys
addMultiset (AddM x c xs) ys = AddM x c (addMultiset xs ys)

||| Explicitly computes the annihilation for a Multiset by merging duplicates.
||| Should be called at the end of an Epoch to compress the state vector.
public export
annihilateMultiset : (Eq a, Num c, Eq c) => Multiset c a -> Multiset c a
annihilateMultiset xs = go ZeroM xs
  where
    go : Multiset c a -> Multiset c a -> Multiset c a
    go acc ZeroM = acc
    go acc (AddM k v rest) = go (insertItem k v acc) rest

||| Computes the total multiplicity (total Leibniz Lag) of the Multiset.
public export
multiplicityAll : (Num c, Abs c) => Multiset c a -> c
multiplicityAll ZeroM = 0
multiplicityAll (AddM x c xs) = abs c + multiplicityAll xs

||| Scalar multiplication: multiplies the multiplicities.
public export
scaleMultiset : (Num c, Eq c) => c -> Multiset c a -> Multiset c a
scaleMultiset scalar xs = if scalar == 0 then ZeroM else go xs
  where
    go : Multiset c a -> Multiset c a
    go ZeroM = ZeroM
    go (AddM k v rest) = AddM k (v * scalar) (go rest)

||| Negation swaps matter and antimatter
public export
negateMultiset : Neg c => Multiset c a -> Multiset c a
negateMultiset ZeroM = ZeroM
negateMultiset (AddM x c xs) = AddM x (-c) (negateMultiset xs)

||| Subtraction (Lazy)
public export
subMultiset : Neg c => Multiset c a -> Multiset c a -> Multiset c a
subMultiset a b = addMultiset a (negateMultiset b)

export
(Eq a, Neg c, Num c, Eq c) => Eq (Multiset c a) where
  a == b = 
    let res = annihilateMultiset (addMultiset a (negateMultiset b))
    in isEmpty res
    where
      isEmpty : {0 b : Type} -> Multiset c b -> Bool
      isEmpty ZeroM = True
      isEmpty _ = False

export
(Show a, Show c) => Show (Multiset c a) where
  show ZeroM = "[]"
  show xs = "[" ++ showItems xs ++ "]"
    where
      showItems : Multiset c a -> String
      showItems ZeroM = ""
      showItems (AddM k v ZeroM) = "(" ++ show k ++ ", " ++ show v ++ ")"
      showItems (AddM k v rest) = "(" ++ show k ++ ", " ++ show v ++ "), " ++ showItems rest

public export
multisetToList : Multiset c a -> List (a, c)
multisetToList ZeroM = []
multisetToList (AddM k v rest) = (k, v) :: multisetToList rest

public export
fromList : (Eq a, Num c, Eq c) => List (a, c) -> Multiset c a
fromList [] = ZeroM
fromList ((k, v) :: rest) = insertItem k v (fromList rest)

-----------------------------------------------------------------------
-- MAXEL & BOX ARITHMETIC MULTIPLICATION (Dynamic Annihilation Policies)
-----------------------------------------------------------------------

||| A Maxel is a Multiset of Pixels, representing transition relations.
public export
0 Maxel : (metric : Metric) -> (c : Type) -> (a : Type) -> Type
Maxel metric c a = Multiset c (Pixel metric a)

||| Dynamic Maxel multiplication (Transitive Product).
||| Multiplies two Maxels element-wise. The product of [a,b] and [c,d] is Just [a,d] if b == c, and Nothing otherwise.
||| The result is a multiset of Maybe (Pixel a) entries, tracking unsuccessful annihilations as Nothing.
public export
mulMaxel : (Eq a, Num c, Eq c) => Maxel metric c a -> Maxel metric c a -> Multiset c (Maybe (Pixel metric a))
mulMaxel ZeroM _ = ZeroM
mulMaxel (AddM p1 c1 rest) m2 =
  addMultiset (mulInner p1 c1 m2) (mulMaxel rest m2)
  where
    mulInner : Pixel metric a -> c -> Maxel metric c a -> Multiset c (Maybe (Pixel metric a))
    mulInner _ _ ZeroM = ZeroM
    mulInner px cx (AddM py cy ys) =
      let pProd = mulPixel px py
          prodCount = cx * cy
      in insertItem pProd prodCount (mulInner px cx ys)

||| Takes the support of a multiplied Maxel.
||| Filters out all 'Nothing' entries (representing annihilated or non-transitive transitions),
||| returning a clean Maxel containing only the valid remaining transitions.
public export
supportMaxel : (Eq a, Num c, Eq c) => Multiset c (Maybe (Pixel metric a)) -> Maxel metric c a
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
data LMultiset : (c : Type) -> (a : Type) -> (contents : List (a, c)) -> Type where
  ||| The vacuum state.
  LEmptyM : LMultiset c a []
  
  ||| Adds an element, strictly consuming the previous state linearly.
  LAddM : {0 rest : List (a, c)} ->
          (item : a) -> 
          (count : c) -> 
          (1 prev : LMultiset c a rest) -> 
          LMultiset c a ((item, count) :: rest)

||| Legacy compatibility alias for LMultiset.
public export
0 LDepMultiset : (c : Type) -> (a : Type) -> (contents : List (a, c)) -> Type
LDepMultiset = LMultiset

||| Tail-recursive helper to freeze a linear multiset into an unrestricted list.
||| The accumulator ensures the linear variable `prev` is consumed in a linear context.
public export
freezeLDepAcc : (acc : List (a, c)) -> (1 m : LMultiset c a contents) -> List (a, c)
freezeLDepAcc acc LEmptyM = acc
freezeLDepAcc acc (LAddM item count prev) = freezeLDepAcc ((item, count) :: acc) prev

||| Freezes a type-level linear multiset back into a standard runtime list.
public export
freezeLDep : {0 contents : List (a, c)} -> (1 m : LMultiset c a contents) -> List (a, c)
freezeLDep m = freezeLDepAcc [] m

||| LUnboxResult: An unrestricted wrapper that preserves the type-level multiset contents.
public export
data LUnboxResult : (c : Type) -> (a : Type) -> List (a, c) -> Type where
  MkLUnboxResult : (x : List (a, c)) -> LUnboxResult c a x

||| Tail-recursive helper to unbox a linear LMultiset, accumulating the elements.
public export total
lunboxLMultisetTail : {0 contents : List (a, c)} -> 
                      (1 m : LMultiset c a contents) -> 
                      (x : List (a, c) ** LUnboxResult c a x)
lunboxLMultisetTail m = go [] m
  where
    go : {0 rest : List (a, c)} -> 
         (acc : List (a, c)) -> 
         (1 prev : LMultiset c a rest) -> 
         (x : List (a, c) ** LUnboxResult c a x)
    go acc LEmptyM = (acc ** MkLUnboxResult acc)
    go acc (LAddM item count prev) = go ((item, count) :: acc) prev

||| Unboxes a linear LMultiset into an unrestricted list of items and counts,
||| preserving its type-level index via structural recursion.
public export
lunboxLMultiset : {0 contents : List (a, c)} -> (1 m : LMultiset c a contents) -> LUnboxResult c a contents
lunboxLMultiset LEmptyM = MkLUnboxResult []
lunboxLMultiset (LAddM item count prev) =
  let MkLUnboxResult prev_un = lunboxLMultiset prev
  in MkLUnboxResult ((item, count) :: prev_un)


||| A linear left fold over an LMultiset, consuming it exactly once.
public export
lfoldl : {0 contents : List (a, c)} ->
         (acc : b) ->
         (f : b -> a -> c -> b) ->
         (1 m : LMultiset c a contents) ->
         b
lfoldl acc f LEmptyM = acc
lfoldl acc f (LAddM item count prev) = lfoldl (f acc item count) f prev

||| A linear right fold over an LMultiset, consuming it exactly once.
public export
lfoldr : {0 contents : List (a, c)} ->
         (f : a -> c -> (1 _ : b) -> b) ->
         (1 acc : b) ->
         (1 m : LMultiset c a contents) ->
         b
lfoldr f acc LEmptyM = acc
lfoldr f acc (LAddM item count prev) = f item count (lfoldr f acc prev)

||| Computes the mapped type index list for lmap.
public export
lmapContents : (a -> b) -> List (a, c) -> List (b, c)
lmapContents f [] = []
lmapContents f ((item, count) :: xs) = (f item, count) :: lmapContents f xs

||| A linear map transforming the values of the multiset in-place.
public export
lmap : {0 contents : List (a, c)} ->
       (f : a -> b) ->
       (1 m : LMultiset c a contents) ->
       LMultiset c b (lmapContents f contents)
lmap f LEmptyM = LEmptyM
lmap f (LAddM item count prev) = LAddM (f item) count (lmap f prev)

||| Destroys / consumes a linear multiset when it is no longer needed.
public export
lconsumeLMultiset : {0 contents : List (a, c)} ->
                    (1 m : LMultiset c a contents) ->
                    ()
lconsumeLMultiset LEmptyM = ()
lconsumeLMultiset (LAddM item count prev) = lconsumeLMultiset prev

||| Linear duplication of a multiset by QTT-compliant copying.
public export total
dupMultiset : (1 _ : Multiset c a) -> (Multiset c a, Multiset c a)
dupMultiset ZeroM = (ZeroM, ZeroM)
dupMultiset (AddM x c xs) =
  let (xs1, xs2) = dupMultiset xs
  in (AddM x c xs1, AddM x c xs2)

||| Linearly consumes a multiset.
public export total
consumeMultiset : (1 _ : Multiset c a) -> ()
consumeMultiset ZeroM = ()
consumeMultiset (AddM x c xs) = consumeMultiset xs

||| Converts a linear Multiset to a list while reconstructing the linear Multiset.
public export total
multisetToListL : (1 _ : Multiset c a) -> LPair (List (a, c)) (Multiset c a)
multisetToListL ZeroM = Builtin.(#) [] ZeroM
multisetToListL (AddM k v rest) =
  let (listRest # restM) = multisetToListL rest
  in Builtin.(#) ((k, v) :: listRest) (AddM k v restM)
