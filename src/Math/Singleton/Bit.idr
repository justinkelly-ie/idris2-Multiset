module Math.Singleton.Bit

import Data.Linear
import Math.Interfaces
import Math.BoxInt
import Math.Multiset
import Math.Singleton.DepSing
import Math.Singleton.Sing

%default total

-----------------------------------------------------------------------
-- THE BY-FIELD B₂ OVER SINGLETON MULTISETS
--
-- Modeled using Wildberger's multiset/singleton theory.
-- BVal is a singleton multiset over the unit coordinate type ()
-- with BoxInt coefficient.
-----------------------------------------------------------------------

||| The two elements of the by-field B₂ represented as a multiset.
public export
BVal : Type
BVal = Sing BoxInt ()

public export
Zero : BVal
Zero = ZeroS

public export
isOne : BVal -> Bool
isOne (OneS () w) = w == 1
isOne _ = False

public export
One : BVal
One = OneS () 1

-----------------------------------------------------------------------
-- BVAL EQUALITY & DISPLAY
-----------------------------------------------------------------------

public export
Ord BVal where
  compare x y =
    case (isOne x, isOne y) of
         (False, False) => EQ
         (False, True)  => LT
         (True, False)  => GT
         (True, True)   => EQ

public export
Show BVal where
  show x = if isOne x then "1" else "0"

-----------------------------------------------------------------------
-- BY-FIELD ARITHMETIC (mod 2) on BVal
-----------------------------------------------------------------------

||| Addition in B₂ (exclusive or).
public export
addBVal : BVal -> BVal -> BVal
addBVal ZeroS y = y
addBVal x ZeroS = x
addBVal x y = if isOne x && isOne y then ZeroS else ZeroS

||| Multiplication in B₂ (logical and).
public export
mulBVal : BVal -> BVal -> BVal
mulBVal x y = if isOne x && isOne y then OneS () 1 else ZeroS

||| Negation in B₂ is the identity: -x = x.
public export
negBVal : BVal -> BVal
negBVal x = x

-----------------------------------------------------------------------
-- NUM / NEG INSTANCES
-----------------------------------------------------------------------

public export
Num BVal where
  (+) = addBVal
  (*) = mulBVal
  fromInteger n = if mod n 2 == 0 then ZeroS else OneS () 1

public export
Neg BVal where
  negate = negBVal
  (-) x y = addBVal x y

-----------------------------------------------------------------------
-- CONVERSION
-----------------------------------------------------------------------

public export
bvalToNat : BVal -> Nat
bvalToNat x = if isOne x then S Z else Z

public export
natToBVal : Nat -> BVal
natToBVal Z     = ZeroS
natToBVal (S Z) = OneS () 1
natToBVal (S (S k)) = natToBVal k

public export
bvalToInteger : BVal -> Integer
bvalToInteger x = if isOne x then 1 else 0

public export
normalize : BVal -> BVal
normalize x = if isOne x then One else Zero

public export
bvalToBoxInt : BVal -> BoxInt
bvalToBoxInt x = if isOne x then 1 else 0

-----------------------------------------------------------------------
-- ABSOLUTE VALUE
-----------------------------------------------------------------------

public export
Abs BVal where
  abs x = x

-----------------------------------------------------------------------
-- LINEAR INSTANCES
-----------------------------------------------------------------------

public export
LConsumable BVal where
  lconsume ZeroS = ()
  lconsume (OneS () n) = ()

public export
LComonoid BVal where
  lcomult ZeroS = Builtin.(#) ZeroS ZeroS
  lcomult (OneS () n) = Builtin.(#) (OneS () n) (OneS () n)

public export
LEq BVal where
  lEq ZeroS ZeroS = Builtin.(#) True  (Builtin.(#) ZeroS ZeroS)
  lEq (OneS () n) (OneS () m) =
    if n == m
      then Builtin.(#) True  (Builtin.(#) (OneS () n) (OneS () m))
      else Builtin.(#) False (Builtin.(#) (OneS () n) (OneS () m))
  lEq ZeroS (OneS () n) = Builtin.(#) False (Builtin.(#) ZeroS (OneS () n))
  lEq (OneS () n) ZeroS = Builtin.(#) False (Builtin.(#) (OneS () n) ZeroS)

-----------------------------------------------------------------------
-- DEPENDENT BIT DEFINITIONS (Box Arithmetic Layer 1)
-----------------------------------------------------------------------

||| A dependently typed bit: a singleton with BVal coefficient.
public export
0 Bit : (a : Type) -> a -> BVal -> Type
Bit a x weight = Math.Singleton.DepSing.Sing BVal a x weight

||| A dependently typed bit restricted strictly to weight One.
public export
0 Bit1 : (a : Type) -> a -> Type
Bit1 a x = Math.Singleton.DepSing.Sing1 BVal a x One

-----------------------------------------------------------------------
-- DEPENDENT BIT ARITHMETIC (BF2-based)
-----------------------------------------------------------------------

||| Addition of two dependent bits at the same coordinate.
public export
addBit : {x : a} -> Bit a x w1 -> Bit a x w2 -> Bit a x (w1 + w2)
addBit (MkDepSing x w1) (MkDepSing x w2) = MkDepSing x (w1 + w2)

||| Addition of a dependent bit and a dependent Bit1 at the same coordinate.
public export
addBitBit1 : {x : a} -> Bit a x w -> Bit1 a x -> Bit a x (w + One)
addBitBit1 (MkDepSing x w) _ = MkDepSing x (w + One)

||| Addition of two dependent Bit1 elements at the same coordinate.
public export
addBit1Bit1 : {x : a} -> Bit1 a x -> Bit1 a x -> Bit a x Zero
addBit1Bit1 _ _ = MkDepSing x Zero
