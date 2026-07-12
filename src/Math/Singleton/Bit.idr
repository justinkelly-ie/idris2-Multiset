module Math.Singleton.Bit

import Data.Linear
import Math.Interfaces
import Math.BoxInt
import Math.Multiset
import Math.Singleton.Sing

%default total

-----------------------------------------------------------------------
-- BIT — THE BIFIED B₂ FIELD
--
-- B₂ = { 0, 1 } represented directly as multisets (Wildberger bification):
--
--   0  =  []    — the empty multiset
--   1  =  [[]]  — the multiset containing one empty multiset
--
-- A Bit IS a Sing BoxInt (Multiset BoxInt Void):
-- a singleton multiset { m } whose one element m ∈ { [], [[]] }.
--
-- Von Neumann ordinal reading:
--   0 := {}         the empty set
--   1 := { {} }     the set containing the empty set
-----------------------------------------------------------------------

||| A Bit is a Sing whose single Multiset element is either
||| [] (zero) or [[]] (one).
public export
Bit : Type
Bit = Sing BoxInt (Multiset BoxInt Void)

||| The zero bit: the singleton { [] }.
||| Represents 0 in B₂.
public export
Zero : Bit
Zero = MkSing ZeroM

||| The one bit: the singleton { [[]] }.
||| Represents 1 in B₂.
public export
One : Bit
One = MkSing (AddM ZeroM 1 ZeroM)

-----------------------------------------------------------------------
-- PREDICATES
-----------------------------------------------------------------------

public export
isZero : Bit -> Bool
isZero (MkSing ZeroM) = True
isZero _              = False

public export
isOne : Bit -> Bool
isOne (MkSing (AddM ZeroM _ ZeroM)) = True
isOne _                              = False

-----------------------------------------------------------------------
-- DISPLAY
-----------------------------------------------------------------------

public export
Show Bit where
  show b = if isOne b then "1" else "0"

-----------------------------------------------------------------------
-- BIT ARITHMETIC (B₂ field, mod 2)
-----------------------------------------------------------------------

||| Addition in B₂: exclusive or (XOR).
||| 0 + 0 = 0,  0 + 1 = 1,  1 + 0 = 1,  1 + 1 = 0
public export
addBit : Bit -> Bit -> Bit
addBit b1 b2 =
  case (isOne b1, isOne b2) of
    (False, False) => Zero
    (False, True)  => One
    (True,  False) => One
    (True,  True)  => Zero

||| Multiplication in B₂: logical AND.
||| 0 * 0 = 0,  0 * 1 = 0,  1 * 0 = 0,  1 * 1 = 1
public export
mulBit : Bit -> Bit -> Bit
mulBit b1 b2 = if isOne b1 && isOne b2 then One else Zero

||| Negation in B₂ is the identity: -x = x.
public export
negBit : Bit -> Bit
negBit x = x

-----------------------------------------------------------------------
-- NUM / NEG INSTANCES
-----------------------------------------------------------------------

public export
Num Bit where
  (+)         = addBit
  (*)         = mulBit
  fromInteger n = if mod n 2 == 0 then Zero else One

public export
Neg Bit where
  negate = negBit
  (-) x y = addBit x y

-----------------------------------------------------------------------
-- ORD
-----------------------------------------------------------------------

public export
Ord Bit where
  compare b1 b2 =
    case (isOne b1, isOne b2) of
      (False, False) => EQ
      (False, True)  => LT
      (True,  False) => GT
      (True,  True)  => EQ

-----------------------------------------------------------------------
-- CONVERSION
-----------------------------------------------------------------------

public export
bitToNat : Bit -> Nat
bitToNat b = if isOne b then S Z else Z

public export
natToBit : Nat -> Bit
natToBit Z         = Zero
natToBit (S Z)     = One
natToBit (S (S k)) = natToBit k

public export
bitToInteger : Bit -> Integer
bitToInteger b = if isOne b then 1 else 0

public export
bitToBoxInt : Bit -> BoxInt
bitToBoxInt b = if isOne b then 1 else 0

public export
normalize : Bit -> Bit
normalize b = if isOne b then One else Zero

-----------------------------------------------------------------------
-- ABSOLUTE VALUE
-----------------------------------------------------------------------

public export
Abs Bit where
  abs x = x

-----------------------------------------------------------------------
-- LINEAR INSTANCES
-----------------------------------------------------------------------

public export
LConsumable Bit where
  lconsume (MkSing ZeroM)               = ()
  lconsume (MkSing (AddM ZeroM _ ZeroM)) = ()
  lconsume (MkSing _)                   = ()

public export
LComonoid Bit where
  lcomult (MkSing ZeroM)               = Builtin.(#) Zero Zero
  lcomult (MkSing (AddM ZeroM n ZeroM)) = Builtin.(#) One  One
  lcomult (MkSing m)                   = Builtin.(#) (MkSing m) (MkSing m)

public export
LEq Bit where
  lEq (MkSing ZeroM)                (MkSing ZeroM)               = Builtin.(#) True  (Builtin.(#) Zero Zero)
  lEq (MkSing (AddM ZeroM n ZeroM)) (MkSing (AddM ZeroM m ZeroM)) = Builtin.(#) True  (Builtin.(#) One  One)
  lEq (MkSing ZeroM)                (MkSing (AddM ZeroM n ZeroM)) = Builtin.(#) False (Builtin.(#) Zero One)
  lEq (MkSing (AddM ZeroM n ZeroM)) (MkSing ZeroM)               = Builtin.(#) False (Builtin.(#) One  Zero)
  lEq b1                            b2                             = Builtin.(#) False (Builtin.(#) b1   b2)
