module Math.Singleton.Bit

import Data.Linear
import Math.Interfaces
import Math.BoxInt
import Math.Multiset
import Math.Singleton.Sing

%default total

-----------------------------------------------------------------------
-- BIT — THE BIFIED B₂ FIELD (Algebra of Boole)
--
-- Bit = Sing (Multiset BoxInt Void)
--
-- A Bit IS a singleton wrapping exactly one Multiset BoxInt Void value.
-- The two canonical B₂ values (Wildberger bification):
--
--   Zero = MkSing ZeroM                 — singleton containing []
--   One  = MkSing (AddM ZeroM 1 ZeroM)  — singleton containing [[]]
--
-- Von Neumann ordinal reading:
--   0 := {}    — the empty set
--   1 := {{}}  — the set containing the empty set
--
-- Algebra of Boole semantics (NOT Boolean algebra):
--
--   negate x = 1 + x   (complement: ¬x = 1 + x)
--   x - y   = x + ¬y   (subtraction via complement)
--
--   Consequence: negate Zero = One, negate One = Zero.
--   This differs from GF(2) where negate x = x.
-----------------------------------------------------------------------

||| A Bit is a singleton containing one Multiset BoxInt (Multiset BoxInt Void) value.
||| The element type is itself a Multiset, enabling the von Neumann bification:
|||   Zero = MkSing ZeroM                  — the empty multiset
|||   One  = MkSing (AddM ZeroM 1 ZeroM)   — the multiset containing [] once
public export
Bit : Type
Bit = Sing (Multiset BoxInt (Multiset BoxInt Void))

||| The zero bit: singleton containing the empty multiset [].
||| Represents 0 in B₂.
public export
Zero : Bit
Zero = MkSing ZeroM

||| The one bit: singleton containing the multiset {[] → 1}.
||| Represents 1 in B₂: the multiset whose single element is ZeroM.
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
isOne (MkSing (AddM _ _ _)) = True   -- any AddM is One (ZeroM is the only other value)
isOne _                     = False

-----------------------------------------------------------------------
-- DISPLAY
-----------------------------------------------------------------------

public export
Show Bit where
  show b = if isOne b then "1" else "0"

-----------------------------------------------------------------------
-- ORD
-- (Eq Bit is provided by the Sing instance: Eq a => Eq (Sing a))
-----------------------------------------------------------------------

public export
Ord Bit where
  compare x y =
    case (isOne x, isOne y) of
      (False, False) => EQ
      (False, True)  => LT
      (True,  False) => GT
      (True,  True)  => EQ

-----------------------------------------------------------------------
-- BIT ARITHMETIC (Algebra of Boole)
--
-- Addition — XOR (mod 2):
--   0+0=0  0+1=1  1+0=1  1+1=0
--
-- Multiplication — AND:
--   0*0=0  0*1=0  1*0=0  1*1=1
--
-- Negation (Algebra of Boole complement):
--   ¬x = 1 + x  =>  ¬0 = 1, ¬1 = 0
--
-- Subtraction:
--   x - y = x + ¬y = x + (1 + y)
-----------------------------------------------------------------------

||| Addition in B₂: XOR.
||| 0+0=0  0+1=1  1+0=1  1+1=0
public export
addBit : Bit -> Bit -> Bit
addBit (MkSing ZeroM) y             = y
addBit x             (MkSing ZeroM) = x
addBit _             _              = Zero

||| Multiplication in B₂: AND.
||| 0*0=0  0*1=0  1*0=0  1*1=1
public export
mulBit : Bit -> Bit -> Bit
mulBit (MkSing ZeroM) _             = Zero
mulBit _             (MkSing ZeroM) = Zero
mulBit x             _              = x

||| Algebra of Boole complement: ¬x = 1 + x.
||| negate Zero = One,  negate One = Zero.
public export
negBit : Bit -> Bit
negBit x = addBit One x

-----------------------------------------------------------------------
-- NUM / NEG INSTANCES
-----------------------------------------------------------------------

public export
Num Bit where
  (+)           = addBit
  (*)           = mulBit
  fromInteger n = if mod n 2 == 0 then Zero else One

||| Neg instance uses the Algebra of Boole complement.
||| negate x = 1 + x   (NOT the GF(2) identity negate x = x)
||| x - y    = x + (1 + y)
public export
Neg Bit where
  negate  = negBit
  (-) x y = addBit x (negBit y)

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
  lconsume (MkSing _) = ()

public export
LComonoid Bit where
  lcomult (MkSing ZeroM) = Builtin.(#) Zero Zero
  lcomult (MkSing m)     = Builtin.(#) (MkSing m) (MkSing m)

public export
LEq Bit where
  lEq (MkSing ZeroM) (MkSing ZeroM) = Builtin.(#) True  (Builtin.(#) Zero Zero)
  lEq (MkSing ZeroM) y              = Builtin.(#) False (Builtin.(#) Zero y)
  lEq x              (MkSing ZeroM) = Builtin.(#) False (Builtin.(#) x    Zero)
  lEq x              y              = Builtin.(#) True  (Builtin.(#) x    y)


