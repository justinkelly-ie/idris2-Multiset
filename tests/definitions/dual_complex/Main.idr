module Main

import QuickCheck
import Math.Interfaces
import Math.BoxInt
import Math.Multiset
import Math.DualComplex

%default total

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

||| Addition is commutative: d1 + d2 = d2 + d1
prop_addCommutative : Property
prop_addCommutative = forAll {a = (DualComplex, DualComplex)} {prop = Bool} arbitrary (MkFn (\(d1, d2) =>
  addDual d1 d2 == addDual d2 d1))

||| Addition identity: d + 0 = d
prop_addIdentity : Property
prop_addIdentity = forAll {a = DualComplex} {prop = Bool} arbitrary (MkFn (\d =>
  addDual d (MkDual 0 0) == d))

||| Addition associativity: (d1 + d2) + d3 = d1 + (d2 + d3)
prop_addAssociative : Property
prop_addAssociative = forAll {a = (DualComplex, DualComplex, DualComplex)} {prop = Bool} arbitrary (MkFn (\(d1, d2, d3) =>
  addDual (addDual d1 d2) d3 == addDual d1 (addDual d2 d3)))

||| Multiplication is commutative: d1 * d2 = d2 * d1
prop_mulCommutative : Property
prop_mulCommutative = forAll {a = (DualComplex, DualComplex)} {prop = Bool} arbitrary (MkFn (\(d1, d2) =>
  mulDual d1 d2 == mulDual d2 d1))

||| Multiplication identity: d * 1 = d
prop_mulIdentity : Property
prop_mulIdentity = forAll {a = DualComplex} {prop = Bool} arbitrary (MkFn (\d =>
  mulDual d (MkDual 1 0) == d))

||| Multiplication associativity: (d1 * d2) * d3 = d1 * (d2 * d3)
prop_mulAssociative : Property
prop_mulAssociative = forAll {a = (DualComplex, DualComplex, DualComplex)} {prop = Bool} arbitrary (MkFn (\(d1, d2, d3) =>
  mulDual (mulDual d1 d2) d3 == mulDual d1 (mulDual d2 d3)))

||| Nilpotency of ε: (0 + 1ε) * (0 + 1ε) = 0 + 0ε
prop_epsNilpotent : Property
prop_epsNilpotent = forAll {a = Bool} {prop = Bool} arbitrary (MkFn (\_ =>
  let eps = MkDual 0 1
  in mulDual eps eps == MkDual 0 0))

||| Distributivity: d1 * (d2 + d3) = (d1 * d2) + (d1 * d3)
prop_distributive : Property
prop_distributive = forAll {a = (DualComplex, DualComplex, DualComplex)} {prop = Bool} arbitrary (MkFn (\(d1, d2, d3) =>
  mulDual d1 (addDual d2 d3) == addDual (mulDual d1 d2) (mulDual d1 d3)))

||| IntPolynumber roundtrip: fromIntPoly (toIntPoly d) = d
prop_intPolyRoundtrip : Property
prop_intPolyRoundtrip = forAll {a = DualComplex} {prop = Bool} arbitrary (MkFn (\d =>
  fromIntPoly (toIntPoly d) == d))

partial
main : IO ()
main = do
  putStrLn ""
  putStrLn "----------------------------------------------------"
  putStrLn "-- Math.DualComplex: Addition & Multiplication Tests --"
  putStrLn "----------------------------------------------------"
  putStrLn ""

  let r1 = quickCheck prop_addCommutative
  putStrLn $ "prop_addCommutative: " ++ r1.msg

  let r2 = quickCheck prop_addIdentity
  putStrLn $ "prop_addIdentity: " ++ r2.msg

  let r3 = quickCheck prop_addAssociative
  putStrLn $ "prop_addAssociative: " ++ r3.msg

  let r4 = quickCheck prop_mulCommutative
  putStrLn $ "prop_mulCommutative: " ++ r4.msg

  let r5 = quickCheck prop_mulIdentity
  putStrLn $ "prop_mulIdentity: " ++ r5.msg

  let r6 = quickCheck prop_mulAssociative
  putStrLn $ "prop_mulAssociative: " ++ r6.msg

  let r7 = quickCheck prop_epsNilpotent
  putStrLn $ "prop_epsNilpotent: " ++ r7.msg

  let r8 = quickCheck prop_distributive
  putStrLn $ "prop_distributive: " ++ r8.msg

  let r9 = quickCheck prop_intPolyRoundtrip
  putStrLn $ "prop_intPolyRoundtrip: " ++ r9.msg

  let results = [r1, r2, r3, r4, r5, r6, r7, r8, r9]
  let failures = filter (\r => isJust r.pass && fromMaybe True r.pass == False) results
  if null failures
    then putStrLn "\nAll 9 DualComplex definition tests passed."
    else idris_crash "FAILURE: One or more DualComplex properties failed."
