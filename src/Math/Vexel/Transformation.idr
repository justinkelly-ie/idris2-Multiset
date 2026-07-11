module Math.Vexel.Transformation

import Math.Multiset
import Math.Singleton.Sing
import Math.Singleton.SingFraction
import Math.Vexel.Vexel
import Math.Vexel.Byte
import Math.BoxInt

%default total

||| Unified state type for logic gates, combining variables and constants.
public export
data LogicState state = VarState state | ConstState TrivialBase

public export
Eq state => Eq (LogicState state) where
  (VarState x) == (VarState y) = x == y
  (ConstState x) == (ConstState y) = x == y
  _ == _ = False

public export
Show state => Show (LogicState state) where
  show (VarState x) = show x
  show (ConstState x) = if x == BaseAnchor then "1" else show x

||| The Transformation MSet (Logic Gate Operator):
||| A multiset of logical relations.
||| Natively mirrors the Maxel (multiset of Pixels) in spatial geometry.
public export
TransformationMSet : (state : Type) -> Type
TransformationMSet state = Multiset BVal (SingRelation (LogicState state))


||| Transitive relation multiplication (Composition).
||| Maps [a -> b] * [c -> d] to [a -> d] iff b == c.
public export
mulRelation : Eq state => SingRelation (LogicState state) -> SingRelation (LogicState state) -> Maybe (SingRelation (LogicState state))
mulRelation (MkSingRelation a b) (MkSingRelation c d) =
  if b == c then Just (MkSingRelation a d) else Nothing

||| Relational multiset multiplication (Transitive product of multisets).
public export
mulTransformation : Eq state => TransformationMSet state -> TransformationMSet state -> TransformationMSet state
mulTransformation ZeroM _ = ZeroM
mulTransformation (AddM r1 c1 rest) m2 =
  annihilateMultiset (addMultiset (mulInner r1 c1 m2) (mulTransformation rest m2))
  where
    mulInner : SingRelation (LogicState state) -> BVal -> TransformationMSet state -> TransformationMSet state
    mulInner _ _ ZeroM = ZeroM
    mulInner r1 c1 (AddM r2 c2 ys) =
      case mulRelation r1 r2 of
        Just rProd => insertItem rProd (mulBVal c1 c2) (mulInner r1 c1 ys)
        Nothing    => mulInner r1 c1 ys

||| Num instance enforcing the Algebra of Boole (+ and *) over Logic Relations.
public export
Eq state => Num (TransformationMSet state) where
  (+) x y = annihilateMultiset (addMultiset x y)
  (*) = mulTransformation
  
  fromInteger 0 = ZeroM
  -- Constant one is a self-loop on the constant base anchor
  fromInteger 1 = AddM (MkSingRelation (ConstState BaseAnchor) (ConstState BaseAnchor)) One ZeroM
  fromInteger _ = ZeroM

public export
wire : LogicState state -> LogicState state -> TransformationMSet state
wire input output = AddM (MkSingRelation input output) One ZeroM

public export
bufferGate : Eq state => LogicState state -> LogicState state -> TransformationMSet state
bufferGate input output = wire input output

||| NOT gate (bias + wire):
||| bias = MkSingRelation (ConstState BaseAnchor) (VarState output)
||| wire = MkSingRelation (VarState input) (VarState output)
public export
notGate : Eq state => LogicState state -> LogicState state -> TransformationMSet state
notGate input output =
  let bias = wire (ConstState BaseAnchor) output
      w    = wire input output
  in bias + w

||| XOR gate (wire1 + wire2):
||| xorGate in1 in2 output = wire in1 output + wire in2 output
public export
xorGate : Eq state => LogicState state -> LogicState state -> LogicState state -> TransformationMSet state
xorGate in1 in2 output =
  wire in1 output + wire in2 output

||| Apply the Transformation MSet to an input state to compute the output state.
||| Uses the new Sing-based modulo-2 parity addition to collapse duplicate targets.
public export
applyTransformation : Eq state => Sing BVal state -> TransformationMSet state -> Sing BVal state
applyTransformation _ ZeroM = ZeroS
applyTransformation inputState (AddM (MkSingRelation src tgt) w rest) =
  let current = case tgt of
                  ConstState _ => ZeroS
                  VarState v   =>
                    case src of
                      ConstState _ =>
                        if not (isOne w) then ZeroS else OneS v w
                      VarState u   =>
                        let c = evaluateSingState inputState u in
                        let val = mulBVal c w in
                        if not (isOne val) then ZeroS else OneS v val
      accumulatedRest = applyTransformation inputState rest
  in current + accumulatedRest

-----------------------------------------------------------------------
-- VEXEL IMPLEMENTATION FOR BOOLE LOGIC (ROW 1 & 2)
-----------------------------------------------------------------------

||| Wrap a single bit-gate singleton multiset into a Byte vector.
public export
toByte : SingBitGateMset state -> Byte state
toByte ZeroS = []
toByte (OneS s w) = [OneS s w]

||| Apply a Transformation MSet (Maxel) to a Byte vector input.
||| Since Byte is a list of singletons, we map applyTransformation over the elements
||| and accumulate the result using addByte.
public export
applyTransformationVexel : Eq state => Byte state -> TransformationMSet state -> Byte state
applyTransformationVexel [] _ = []
applyTransformationVexel (x :: xs) trans =
  let res = applyTransformation x trans
      tailRes = applyTransformationVexel xs trans
  in addByte (toByte res) tailRes
