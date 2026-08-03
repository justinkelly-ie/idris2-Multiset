module Main

import QuickCheck
import Data.Linear
import Math.Interfaces
import Math.BoxInt
import Math.Multiset
import Math.DualComplex
import Math.Infinitesimal

%default total

public export
Arbitrary PolyNumber where
  arbitrary = do
    c0 <- arbitrary {a = Integer}
    c1 <- arbitrary {a = Integer}
    c2 <- arbitrary {a = Integer}
    let raw = [(0, fromInteger c0), (1, fromInteger c1), (2, fromInteger c2)]
        nonZero = filter (\(_, v) => let (MkUr val) = boxToInt v in val /= 0) raw
    pure (fromList nonZero)
  coarbitrary p gen = gen

public export
Arbitrary DualComplex where
  arbitrary = do
    r <- arbitrary {a = Integer}
    e <- arbitrary {a = Integer}
    pure (MkDual (fromInteger r) (fromInteger e))
  coarbitrary (MkDual r e) gen =
    let (MkUr rVal) = boxToInt r
        (MkUr eVal) = boxToInt e
    in coarbitrary rVal (coarbitrary eVal gen)

||| PolyNumber addition is commutative: P1 + P2 = P2 + P1
prop_addCommutative : Property
prop_addCommutative = forAll {a = (PolyNumber, PolyNumber)} {prop = Bool} arbitrary (MkFn (\(p1, p2) =>
  annihilateMultiset (addMultiset p1 p2) == annihilateMultiset (addMultiset p2 p1)))

||| PolyNumber addition identity: P + 0 = P
prop_addIdentity : Property
prop_addIdentity = forAll {a = PolyNumber} {prop = Bool} arbitrary (MkFn (\p =>
  annihilateMultiset (addMultiset p ZeroM) == annihilateMultiset p))

||| PolyNumber multiplication is commutative: P1 * P2 = P2 * P1
prop_mulCommutative : Property
prop_mulCommutative = forAll {a = (PolyNumber, PolyNumber)} {prop = Bool} arbitrary (MkFn (\(p1, p2) =>
  annihilateMultiset (mulPoly p1 p2) == annihilateMultiset (mulPoly p2 p1)))

||| PolyNumber multiplication identity: P * (1·α⁰) = P
prop_mulIdentity : Property
prop_mulIdentity = forAll {a = PolyNumber} {prop = Bool} arbitrary (MkFn (\p =>
  let unitPoly = AddM 0 1 ZeroM
  in annihilateMultiset (mulPoly p unitPoly) == annihilateMultiset p))

||| Algebraic Product Rule: ∂(P1 * P2) = P1 * ∂P2 + P2 * ∂P1
prop_productRuleFaulhaber : Property
prop_productRuleFaulhaber = forAll {a = (PolyNumber, PolyNumber)} {prop = Bool} arbitrary (MkFn (\(p1, p2) =>
  let derivProduct = derivePoly (mulPoly p1 p2)
      rhs = addMultiset (mulPoly p1 (derivePoly p2)) (mulPoly p2 (derivePoly p1))
  in annihilateMultiset derivProduct == annihilateMultiset rhs))

||| Dual Evaluation Product Homomorphism: evalDual (P1 * P2) d = mulDual (evalDual P1 d) (evalDual P2 d)
prop_evalDualProductHomomorphism : Property
prop_evalDualProductHomomorphism = forAll {a = (PolyNumber, PolyNumber, DualComplex)} {prop = Bool} arbitrary (MkFn (\(p1, p2, d) =>
  evalDual (mulPoly p1 p2) d == mulDual (evalDual p1 d) (evalDual p2 d)))

||| Dual Evaluation Addition Homomorphism: evalDual (P1 + P2) d = addDual (evalDual P1 d) (evalDual P2 d)
prop_evalDualAdditionHomomorphism : Property
prop_evalDualAdditionHomomorphism = forAll {a = (PolyNumber, PolyNumber, DualComplex)} {prop = Bool} arbitrary (MkFn (\(p1, p2, d) =>
  evalDual (addMultiset p1 p2) d == addDual (evalDual p1 d) (evalDual p2 d)))

partial
main : IO ()
main = do
  putStrLn ""
  putStrLn "----------------------------------------------------"
  putStrLn "-- Math.Infinitesimal: Addition & Multiplication Tests --"
  putStrLn "----------------------------------------------------"
  putStrLn ""

  let r1 = quickCheck prop_addCommutative
  putStrLn $ "prop_addCommutative: " ++ r1.msg

  let r2 = quickCheck prop_addIdentity
  putStrLn $ "prop_addIdentity: " ++ r2.msg

  let r3 = quickCheck prop_mulCommutative
  putStrLn $ "prop_mulCommutative: " ++ r3.msg

  let r4 = quickCheck prop_mulIdentity
  putStrLn $ "prop_mulIdentity: " ++ r4.msg

  let r5 = quickCheck prop_productRuleFaulhaber
  putStrLn $ "prop_productRuleFaulhaber: " ++ r5.msg

  let r6 = quickCheck prop_evalDualProductHomomorphism
  putStrLn $ "prop_evalDualProductHomomorphism: " ++ r6.msg

  let r7 = quickCheck prop_evalDualAdditionHomomorphism
  putStrLn $ "prop_evalDualAdditionHomomorphism: " ++ r7.msg

  let results = [r1, r2, r3, r4, r5, r6, r7]
  let failures = filter (\r => isJust r.pass && fromMaybe True r.pass == False) results
  if null failures
    then putStrLn "\nAll 7 Infinitesimal definition tests passed."
    else idris_crash "FAILURE: One or more Infinitesimal properties failed."
