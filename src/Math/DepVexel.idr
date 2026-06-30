module Math.DepVexel

import Math.Sing
import Data.List

%default covering

||| A dependently typed Vexel where singleton tokens are tracked at the type level.
public export
data DepVexel : (c : Type) -> (a : Type) -> (contents : List (Sing c a)) -> Type where
  ||| The empty Vexel state.
  DepEmptyV : DepVexel c a []
  
  ||| Adds a singleton token to the Vexel.
  DepAddV : (token : Sing c a) ->
            {0 rest : List (Sing c a)} ->
            (prev : DepVexel c a rest) ->
            DepVexel c a (token :: rest)

||| Freezes a dependently typed Vexel back into a standard runtime list of singletons.
public export
freezeDepVexel : {0 contents : List (Sing c a)} -> DepVexel c a contents -> List (Sing c a)
freezeDepVexel DepEmptyV = []
freezeDepVexel (DepAddV token prev) = token :: freezeDepVexel prev
