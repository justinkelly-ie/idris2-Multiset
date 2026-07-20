module Main

import QuickCheck
import Math.Multiset
import Math.BoxInt
import Math.Singleton.Sing
import Math.Singleton.Bit

%default total

--------------------------------------------------------------------------------
-- ARBITRARY INSTANCE FOR Bit
--
-- Bit = Sing BoxInt (Multiset BoxInt Void)
-- Two values: Zero = MkSing ZeroM, One = MkSing (AddM ZeroM 1 ZeroM)
--------------------------------------------------------------------------------

public export
Arbitrary Bit where
  arbitrary = do
    b <- arbitrary {a = Bool}
    pure (if b then One else Zero)
  coarbitrary b gen =
    if isOne b then variant 1 gen else variant 0 gen

--------------------------------------------------------------------------------
-- DEFINITIONS: CANONICAL VALUES
--------------------------------------------------------------------------------

||| Zero is not One.
prop_zeroNeOne : Property
prop_zeroNeOne = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  not (isOne Zero)))

||| One is not Zero.
prop_oneNeZero : Property
prop_oneNeZero = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  isOne One))

||| Zero is the Sing wrapping the empty multiset [].
prop_zeroIsEmptyMultiset : Property
prop_zeroIsEmptyMultiset = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  fromSing Zero == the (Multiset BoxInt Void) ZeroM))

||| One is the Sing wrapping [[]] — the multiset containing one empty multiset.
prop_oneIsUnitMultiset : Property
prop_oneIsUnitMultiset = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  fromSing One == the (Multiset BoxInt Void) (AddM ZeroM 1 ZeroM)))

--------------------------------------------------------------------------------
-- FIELD AXIOMS FOR B₂
--------------------------------------------------------------------------------

||| Addition is commutative: x + y = y + x.
prop_addCommutative : Property
prop_addCommutative = forAll {a = (Bit, Bit)} {prop = Bool} arbitrary (MkFn (\(x, y) =>
  (x + y) == (y + x)))

||| Zero is the additive identity: x + 0 = x.
prop_addIdentity : Property
prop_addIdentity = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  (x + Zero) == x))

||| Every element is self-inverse under addition: x + x = 0 (XOR in B₂).
prop_addSelfAnnihilates : Property
prop_addSelfAnnihilates = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  (x + x) == Zero))

||| Multiplication is commutative: x * y = y * x.
prop_mulCommutative : Property
prop_mulCommutative = forAll {a = (Bit, Bit)} {prop = Bool} arbitrary (MkFn (\(x, y) =>
  (x * y) == (y * x)))

||| One is the multiplicative identity: x * 1 = x.
prop_mulIdentity : Property
prop_mulIdentity = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  (x * One) == x))

||| Zero annihilates under multiplication: x * 0 = 0.
prop_mulZeroAnnihilates : Property
prop_mulZeroAnnihilates = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  (x * Zero) == Zero))

||| Multiplication is idempotent in B₂: x * x = x.
prop_mulIdempotent : Property
prop_mulIdempotent = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  (x * x) == x))

||| Distributivity: x * (y + z) = (x * y) + (x * z).
prop_distributive : Property
prop_distributive = forAll {a = (Bit, Bit, Bit)} {prop = Bool} arbitrary (MkFn (\(x, y, z) =>
  (x * (y + z)) == ((x * y) + (x * z))))

||| Negation is involutive: -(-x) = x.
prop_negInvolutive : Property
prop_negInvolutive = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  negate (negate x) == x))

||| Subtraction in Algebra of Boole: x - y = x + 1 + y.
prop_subIsComplementAdd : Property
prop_subIsComplementAdd = forAll {a = (Bit, Bit)} {prop = Bool} arbitrary (MkFn (\(x, y) =>
  (x - y) == (x + One + y)))

--------------------------------------------------------------------------------
-- CONVERSION ROUND-TRIPS
--------------------------------------------------------------------------------

||| natToBit . bitToNat is the identity.
prop_natRoundTrip : Property
prop_natRoundTrip = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  natToBit (bitToNat x) == x))

||| fromInteger round-trip: fromInteger 0 = Zero, fromInteger 1 = One.
prop_fromIntegerZero : Property
prop_fromIntegerZero = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  the Bit (fromInteger 0) == Zero))

prop_fromIntegerOne : Property
prop_fromIntegerOne = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  the Bit (fromInteger 1) == One))

||| fromInteger is mod-2: fromInteger 2 = Zero, fromInteger 3 = One.
prop_fromIntegerMod2 : Property
prop_fromIntegerMod2 = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  (the Bit (fromInteger 2) == Zero) && (the Bit (fromInteger 3) == One)))

||| bitToBoxInt: Zero -> 0, One -> 1.
prop_bitToBoxInt : Property
prop_bitToBoxInt = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  (bitToBoxInt Zero == (0 : BoxInt)) && (bitToBoxInt One == (1 : BoxInt))))

||| normalize is the identity on canonical values.
prop_normalizeIdempotent : Property
prop_normalizeIdempotent = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  normalize (normalize x) == normalize x))

--------------------------------------------------------------------------------
-- SING EMBEDDING
--------------------------------------------------------------------------------

||| toSing . fromSing is the identity on a Bit viewed as a Sing.
prop_singEmbedding : Property
prop_singEmbedding = forAll {a = Bit} {prop = Bool} arbitrary (MkFn (\x =>
  toSing (fromSing x) == x))

--------------------------------------------------------------------------------
-- TEST RUNNER
--------------------------------------------------------------------------------

partial
main : IO ()
main = do
  putStrLn ""
  putStrLn "----------------------------------------------------"
  putStrLn "-- Math.Singleton.Bit: Bified B₂ Definition Tests --"
  putStrLn "----------------------------------------------------"
  putStrLn ""

  let r1  = quickCheck prop_zeroNeOne
  putStrLn $ "prop_zeroNeOne: " ++ r1.msg

  let r2  = quickCheck prop_oneNeZero
  putStrLn $ "prop_oneNeZero: " ++ r2.msg

  let r3  = quickCheck prop_zeroIsEmptyMultiset
  putStrLn $ "prop_zeroIsEmptyMultiset: " ++ r3.msg

  let r4  = quickCheck prop_oneIsUnitMultiset
  putStrLn $ "prop_oneIsUnitMultiset: " ++ r4.msg

  let r5  = quickCheck prop_addCommutative
  putStrLn $ "prop_addCommutative: " ++ r5.msg

  let r6  = quickCheck prop_addIdentity
  putStrLn $ "prop_addIdentity: " ++ r6.msg

  let r7  = quickCheck prop_addSelfAnnihilates
  putStrLn $ "prop_addSelfAnnihilates: " ++ r7.msg

  let r8  = quickCheck prop_mulCommutative
  putStrLn $ "prop_mulCommutative: " ++ r8.msg

  let r9  = quickCheck prop_mulIdentity
  putStrLn $ "prop_mulIdentity: " ++ r9.msg

  let r10 = quickCheck prop_mulZeroAnnihilates
  putStrLn $ "prop_mulZeroAnnihilates: " ++ r10.msg

  let r11 = quickCheck prop_mulIdempotent
  putStrLn $ "prop_mulIdempotent: " ++ r11.msg

  let r12 = quickCheck prop_distributive
  putStrLn $ "prop_distributive: " ++ r12.msg

  let r13 = quickCheck prop_negInvolutive
  putStrLn $ "prop_negInvolutive: " ++ r13.msg

  let r14 = quickCheck prop_subIsComplementAdd
  putStrLn $ "prop_subIsComplementAdd: " ++ r14.msg

  let r15 = quickCheck prop_natRoundTrip
  putStrLn $ "prop_natRoundTrip: " ++ r15.msg

  let r16 = quickCheck prop_fromIntegerZero
  putStrLn $ "prop_fromIntegerZero: " ++ r16.msg

  let r17 = quickCheck prop_fromIntegerOne
  putStrLn $ "prop_fromIntegerOne: " ++ r17.msg

  let r18 = quickCheck prop_fromIntegerMod2
  putStrLn $ "prop_fromIntegerMod2: " ++ r18.msg

  let r19 = quickCheck prop_bitToBoxInt
  putStrLn $ "prop_bitToBoxInt: " ++ r19.msg

  let r20 = quickCheck prop_normalizeIdempotent
  putStrLn $ "prop_normalizeIdempotent: " ++ r20.msg

  let r21 = quickCheck prop_singEmbedding
  putStrLn $ "prop_singEmbedding: " ++ r21.msg

  let results = [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21]
  let failures = filter (\r => isJust r.pass && fromMaybe True r.pass == False) results
  if null failures
    then putStrLn "\nAll 21 tests passed."
    else idris_crash "FAILURE: One or more Bit properties failed."
