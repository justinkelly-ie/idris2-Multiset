module Math.Singleton.SingFraction

import Math.Multiset
import Math.Singleton.Sing
import Math.BoxInt
import public Math.Singleton.Bit

%default total

public export
0 TrivialBase : Type
TrivialBase = Nat

public export
BaseAnchor : TrivialBase
BaseAnchor = 0


||| A type alias for a Singleton Bit-Gate Multiset.
||| Defined directly as the Sing multiset with weights BVal.
public export
SingBitGateMset : (state : Type) -> Type
SingBitGateMset state = Sing BVal state

||| The empty (zero) singleton bit-gate state.
public export
emptySingBitGate : SingBitGateMset state
emptySingBitGate = ZeroS

||| Insert a state with a given BVal weight into the singleton bit-gate multiset.
public export
insertSingBit : Eq state => state -> BVal -> SingBitGateMset state -> SingBitGateMset state
insertSingBit s w m =
  if w == Zero then m else OneS s w

||| Evaluate the binary flag for a state in the singleton bit-gate multiset.
public export
evaluateSingState : Eq state => SingBitGateMset state -> state -> BVal
evaluateSingState ZeroS _ = Zero
evaluateSingState (OneS k v) s =
  if k == s
    then v
    else Zero

||| A singleton Boole Fraction type.
||| Establishes type-level division-by-zero protection using strictly positive Sing1.
public export
record SingBooleFraction (state : Type) where
  constructor OverSingCircuit
  numeratorBitMset : SingBitGateMset state
  denominatorUnit  : Sing1 BVal TrivialBase

||| Canonical unit denominator singleton multiset.
public export
theSingUnitConstant : Sing1 BVal TrivialBase
theSingUnitConstant = MkSing1 BaseAnchor One

||| Smart constructor: builds a SingBooleFraction with the strictly positive unit denominator.
public export
mkSingBooleFraction : SingBitGateMset state -> SingBooleFraction state
mkSingBooleFraction bits = OverSingCircuit bits theSingUnitConstant

||| Evaluate a state from the singleton fraction.
public export
evalSingFraction : Eq state => SingBooleFraction state -> state -> BVal
evalSingFraction (OverSingCircuit num _) s = evaluateSingState num s

||| Lift the singleton multiset to BoxInt weights.
public export
liftSingBitGateToBoxInt : SingBitGateMset state -> Sing BoxInt state
liftSingBitGateToBoxInt ZeroS = ZeroS
liftSingBitGateToBoxInt (OneS k v) = OneS k (bvalToBoxInt v)

||| Lift the singleton fraction to BoxInt, transitioning to Row 2.
public export
liftSingToRow2 : SingBooleFraction state -> Sing BoxInt state
liftSingToRow2 (OverSingCircuit num _) = liftSingBitGateToBoxInt num
