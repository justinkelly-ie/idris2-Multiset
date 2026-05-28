module Math.Interfaces

import Data.Linear

%default total

public export
implementation (Show a, Show b) => Show (LPair a b) where
  show (x # y) = "(" ++ show x ++ " # " ++ show y ++ ")"

-----------------------------------------------------------------------
-- 1. CORE LINEAR INTERFACES
-----------------------------------------------------------------------

||| LConsumable: A protocol for destroying linear resources.
public export
interface LConsumable a where
  lconsume : (1 _ : a) -> ()

||| LComonoid: A protocol for duplicating linear resources.
||| We use LPair (Builtin.(#)) to ensure Idris 2 QTT compliance.
public export
interface LConsumable a => LComonoid a where
  lcounit : (1 _ : a) -> ()
  lcounit x = lconsume x
  
  lcomult : (1 _ : a) -> LPair a a

||| LEq: A linear version of Boolean equality.
||| Returns a linear pair of the result and the consumed resources.
public export
interface (LComonoid a) => LEq a where
  lEq : (1 _ : a) -> (1 _ : a) -> LPair Bool (LPair a a)

-----------------------------------------------------------------------
-- 2. STANDARD IMPLEMENTATIONS
-----------------------------------------------------------------------

||| Linear Integer Consumption: Uses a lambda bridge to satisfy QTT.
public export
lconsumeInt : (1 _ : Integer) -> ()
lconsumeInt = believe_me (\x : Integer => ())

||| Linear Integer Duplication: Uses a lambda bridge to satisfy QTT.
public export
lcomultInt : (1 _ : Integer) -> LPair Integer Integer
lcomultInt = believe_me (\x : Integer => Builtin.(#) x x)

||| Linear Integer Equality: Uses a lambda bridge to satisfy QTT.
public export
lEqInt : (1 _ : Integer) -> (1 _ : Integer) -> LPair Bool (LPair Integer Integer)
lEqInt = believe_me (\x : Integer, y : Integer => Builtin.(#) (x == y) (Builtin.(#) x y))

public export
implementation LConsumable Integer where
  lconsume = lconsumeInt

public export
implementation LComonoid Integer where
  lcomult = lcomultInt

public export
implementation LEq Integer where
  lEq = lEqInt

||| Linear Nat Consumption: Uses structural induction.
public export
lconsumeNat : (1 _ : Nat) -> ()
lconsumeNat Z = ()
lconsumeNat (S k) = lconsumeNat k

||| Linear Nat Duplication: Uses structural induction.
public export
lcomultNat : (1 _ : Nat) -> LPair Nat Nat
lcomultNat Z = Builtin.(#) Z Z
lcomultNat (S k) = let Builtin.(#) k1 k2 = lcomultNat k in Builtin.(#) (S k1) (S k2)

||| Linear Nat Equality: Uses structural induction.
public export
lEqNat : (1 _ : Nat) -> (1 _ : Nat) -> LPair Bool (LPair Nat Nat)
lEqNat Z Z = Builtin.(#) True (Builtin.(#) Z Z)
lEqNat (S k) (S j) = let Builtin.(#) res (Builtin.(#) k1 j1) = lEqNat k j in Builtin.(#) res (Builtin.(#) (S k1) (S j1))
lEqNat Z (S j) = Builtin.(#) False (Builtin.(#) Z (S j))
lEqNat (S k) Z = Builtin.(#) False (Builtin.(#) (S k) Z)

public export
implementation LConsumable Nat where
  lconsume = lconsumeNat

public export
implementation LComonoid Nat where
  lcomult = lcomultNat

public export
implementation LEq Nat where
  lEq = lEqNat

public export
implementation LConsumable () where
  lconsume () = ()

public export
implementation LComonoid () where
  lcomult () = Builtin.(#) () ()

public export
implementation LEq () where
  lEq () () = Builtin.(#) True (Builtin.(#) () ())

public export
implementation LConsumable Bool where
  lconsume True = ()
  lconsume False = ()

public export
implementation LComonoid Bool where
  lcomult True = Builtin.(#) True True
  lcomult False = Builtin.(#) False False

public export
implementation (LConsumable a, LConsumable b) => LConsumable (LPair a b) where
  lconsume (x # y) = case lconsume x of () => lconsume y

public export
implementation (LComonoid a, LComonoid b) => LComonoid (LPair a b) where
  lcomult (x # y) = 
    let Builtin.(#) x1 x2 = lcomult x
        Builtin.(#) y1 y2 = lcomult y
    in Builtin.(#) (x1 # y1) (x2 # y2)

public export
implementation (LEq a, LEq b) => LEq (LPair a b) where
  lEq (l1 # r1) (l2 # r2) = 
    let Builtin.(#) resL (Builtin.(#) l1' l2') = lEq l1 l2
        Builtin.(#) resR (Builtin.(#) r1' r2') = lEq r1 r2
        res = if resL then resR else case lconsume resR of () => False
    in Builtin.(#) res (Builtin.(#) (l1' # r1') (l2' # r2'))
