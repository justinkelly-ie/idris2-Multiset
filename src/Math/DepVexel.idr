module Math.DepVexel

import Data.List
import Math.DepSing
import Math.Sing

%default total

||| A dependently typed Vexel where coordinates and weights are tracked at the type level.
public export
data DepVexel : (c : Type) -> (a : Type) -> List (a, c) -> Type where
  ||| The empty Vexel state.
  DepEmptyV : DepVexel c a []
  
  ||| Adds a dependent singleton to the Vexel.
  DepAddV : {x : a} -> {weight : c} ->
            DepSing c a x weight ->
            {rest : List (a, c)} ->
            DepVexel c a rest ->
            DepVexel c a ((x, weight) :: rest)

||| Freezes a dependently typed Vexel back into a standard runtime list of coordinate-weight pairs.
public export
freezeDepVexel : {0 contents : List (a, c)} -> DepVexel c a contents -> List (a, c)
freezeDepVexel DepEmptyV = []
freezeDepVexel (DepAddV (MkDepSing x weight) prev) = (x, weight) :: freezeDepVexel prev

||| Maps a runtime Vexel (list of singletons) to a type-level association list of active coordinate-weight pairs.
public export
0 vexelToMSet : List (Sing c a) -> List (a, c)
vexelToMSet [] = []
vexelToMSet (ZeroS :: xs) = vexelToMSet xs
vexelToMSet (OneS x weight :: xs) = (x, weight) :: vexelToMSet xs
