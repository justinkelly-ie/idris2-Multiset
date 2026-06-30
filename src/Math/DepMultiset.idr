module Math.DepMultiset

import Math.Multiset
import Data.List

%default covering

||| A dependently typed signed multiset where the elements and counts are tracked at the type level.
||| Unlike LMultiset, this does not enforce QTT linear (1) constraints.
public export
data DepMultiset : (c : Type) -> (a : Type) -> (contents : List (a, c)) -> Type where
  ||| The vacuum state.
  DepEmptyM : DepMultiset c a []
  
  ||| Adds an element without linear resource consumption.
  DepAddM : {0 rest : List (a, c)} ->
            (item : a) -> 
            (count : c) -> 
            (prev : DepMultiset c a rest) -> 
            DepMultiset c a ((item, count) :: rest)

||| Freezes a type-level dependent multiset into a standard runtime list.
public export
freezeDep : {0 contents : List (a, c)} -> DepMultiset c a contents -> List (a, c)
freezeDep DepEmptyM = []
freezeDep (DepAddM item count prev) = (item, count) :: freezeDep prev

||| A standard left fold over a DepMultiset.
public export
depFoldl : {0 contents : List (a, c)} ->
           (acc : b) ->
           (f : b -> a -> c -> b) ->
           DepMultiset c a contents ->
           b
depFoldl acc f DepEmptyM = acc
depFoldl acc f (DepAddM item count prev) = depFoldl (f acc item count) f prev

||| A standard right fold over a DepMultiset.
public export
depFoldr : {0 contents : List (a, c)} ->
           (f : a -> c -> b -> b) ->
           (acc : b) ->
           DepMultiset c a contents ->
           b
depFoldr f acc DepEmptyM = acc
depFoldr f acc (DepAddM item count prev) = f item count (depFoldr f acc prev)

||| Computes the mapped type index list for depMap.
public export
depMapContents : (a -> b) -> List (a, c) -> List (b, c)
depMapContents f [] = []
depMapContents f ((item, count) :: xs) = (f item, count) :: depMapContents f xs

||| A standard map transforming the values of the multiset in-place.
public export
depMap : {0 contents : List (a, c)} ->
         (f : a -> b) ->
         DepMultiset c a contents ->
         DepMultiset c b (depMapContents f contents)
depMap f DepEmptyM = DepEmptyM
depMap f (DepAddM item count prev) = DepAddM (f item) count (depMap f prev)
