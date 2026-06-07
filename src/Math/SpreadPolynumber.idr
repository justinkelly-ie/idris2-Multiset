module Math.SpreadPolynumber

import Data.Linear
import Math.Interfaces
import Math.Polynumber
import Math.IntPolynumber
import Data.List

%default total

||| Multiply an IntPolynumber by a scalar constant.
export covering
scalarMul : Nat -> IntPolynumber -> IntPolynumber
scalarMul Z p = emptyIntPoly
scalarMul (S k) p = addIntPoly p (scalarMul k p)

||| Representation of the spread variable `s` as a polynomial: alpha^1 beta^0
export
sPoly : IntPolynumber
sPoly = posTerm 1 0 1

||| The constant polynomial `1`
export
onePoly : IntPolynumber
onePoly = posTerm 0 0 1

||| Generate the n-th Spread Polynomial recursively.
||| S_0(s) = 0
||| S_1(s) = s
||| S_n(s) = 2(1-2s) S_{n-1}(s) - S_{n-2}(s) + 2s
export covering
spreadPoly : Nat -> IntPolynumber
spreadPoly Z = emptyIntPoly
spreadPoly (S Z) = sPoly
spreadPoly (S (S k)) =
  let sn1 = spreadPoly (S k)
      sn2 = spreadPoly k
      
      -- We construct `1 - 2s`
      oneMinus2s = subIntPoly onePoly (scalarMul 2 sPoly)
      
      -- part1 = 2 * (1 - 2s) * sn1
      part1 = scalarMul 2 (mulIntPoly oneMinus2s sn1)
      
      -- part3 = 2s
      twoS = scalarMul 2 sPoly
      
      -- combine: part1 - sn2 + part3
  in annihilateIntPoly (addIntPoly (subIntPoly part1 sn2) twoS)

||| Iterative (bottom-up) approach for generating the n-th Spread Polynomial.
||| Computes in O(N) time instead of O(2^N) by keeping the last two results.
export covering
memoSpreadPoly : Nat -> IntPolynumber
memoSpreadPoly Z = emptyIntPoly
memoSpreadPoly (S Z) = sPoly
memoSpreadPoly (S (S n)) =
  let oneMinus2s = subIntPoly onePoly (scalarMul 2 sPoly)
      twoS = scalarMul 2 sPoly
      
      step : Nat -> (IntPolynumber, IntPolynumber) -> (IntPolynumber, IntPolynumber)
      step Z state = state
      step (S k) (sn1, sn2) =
          let part1 = scalarMul 2 (mulIntPoly oneMinus2s sn1)
              sn = annihilateIntPoly (addIntPoly (subIntPoly part1 sn2) twoS)
          in step k (sn, sn1)
      in fst (step n (sPoly, emptyIntPoly))

||| Explicit definitions for n=1 to 13 as required by the knowledge base.
export covering S1 : IntPolynumber; S1 = spreadPoly 1
export covering S2 : IntPolynumber; S2 = spreadPoly 2
export covering S3 : IntPolynumber; S3 = spreadPoly 3
export covering S4 : IntPolynumber; S4 = spreadPoly 4
export covering S5 : IntPolynumber; S5 = spreadPoly 5
export covering S6 : IntPolynumber; S6 = spreadPoly 6
export covering S7 : IntPolynumber; S7 = spreadPoly 7
export covering S8 : IntPolynumber; S8 = spreadPoly 8
export covering S9 : IntPolynumber; S9 = spreadPoly 9
export covering S10 : IntPolynumber; S10 = spreadPoly 10
export covering S11 : IntPolynumber; S11 = spreadPoly 11
export covering S12 : IntPolynumber; S12 = spreadPoly 12
export covering S13 : IntPolynumber; S13 = spreadPoly 13

-----------------------------------------------------------------------
-- INDUCTIVE SYMBOLIC SPREAD POLYNOMIAL EXPRESSION REPRESENTATION
--
-- Lets the universe "speak for itself" by modeling the symbolic structure
-- of Chebyshev recurrence relations at the type/data level.
-----------------------------------------------------------------------

||| An inductive datatype representing the symbolic recurrence relations of Spread Polynomials.
||| Each constructor represents a fundamental step in the algebraic generation:
||| - SZero represents S_0(s) = 0
||| - SOne represents S_1(s) = s
||| - SRec represents S_n(s) = 2(1-2s) S_{n-1}(s) - S_{n-2}(s) + 2s
public export
data SpreadPolyExpr : Nat -> Type where
  SZero : SpreadPolyExpr 0
  SOne  : SpreadPolyExpr 1
  SRec  : (k : Nat) -> (sn1 : SpreadPolyExpr (S k)) -> (sn2 : SpreadPolyExpr k) -> SpreadPolyExpr (S (S k))

||| Evaluates a symbolic SpreadPolyExpr into a concrete IntPolynumber.
export covering
evalSpreadPolyExpr : SpreadPolyExpr n -> IntPolynumber
evalSpreadPolyExpr SZero = emptyIntPoly
evalSpreadPolyExpr SOne = sPoly
evalSpreadPolyExpr (SRec k sn1 sn2) =
  let p1 = evalSpreadPolyExpr sn1
      p2 = evalSpreadPolyExpr sn2
      oneMinus2s = subIntPoly onePoly (scalarMul 2 sPoly)
      part1 = scalarMul 2 (mulIntPoly oneMinus2s p1)
      twoS = scalarMul 2 sPoly
  in annihilateIntPoly (addIntPoly (subIntPoly part1 p2) twoS)

||| Automatically constructs the canonical symbolic SpreadPolyExpr for a given degree.
export covering
makeSpreadPolyExpr : (n : Nat) -> SpreadPolyExpr n
makeSpreadPolyExpr Z = SZero
makeSpreadPolyExpr (S Z) = SOne
makeSpreadPolyExpr (S (S k)) = SRec k (makeSpreadPolyExpr (S k)) (makeSpreadPolyExpr k)

-----------------------------------------------------------------------
-- GOH FACTORISATION
-----------------------------------------------------------------------

private
gcdInteger : Integer -> Integer -> Integer
gcdInteger a 0 = abs a
gcdInteger a b = gcdInteger b (assert_smaller b (a `mod` b))

private
totient : Nat -> Nat
totient Z = Z
totient (S Z) = S Z
totient n =
  let nVal = cast n
      candidates = [1 .. (nVal - 1)]
      coprimes = filter (\k => gcdInteger nVal k == 1) candidates
  in length coprimes

private
divisors : Nat -> List Nat
divisors Z = []
divisors n =
  let nVal = cast n
      candidates = [1 .. nVal]
      divs = filter (\k => nVal `mod` k == 0) candidates
  in map cast divs

private
polyDegree : IntPolynumber -> Nat
polyDegree ZeroM = 0
polyDegree (AddM (alpha, beta) coeff rest) =
  let restDeg = polyDegree rest
  in if coeff == 0 then restDeg else max alpha restDeg

private
getCoefficient : Nat -> IntPolynumber -> Integer
getCoefficient power ZeroM = 0
getCoefficient power (AddM (alpha, beta) coeff rest) =
  if alpha == power then coeff + getCoefficient power rest
  else getCoefficient power rest

private
polyToCoeffs : IntPolynumber -> List Integer
polyToCoeffs p =
  let deg = polyDegree p
  in map (\power => getCoefficient power p) [0 .. deg]

private
coeffsToPoly : List Integer -> IntPolynumber
coeffsToPoly coeffs = go 0 coeffs
  where
    go : Nat -> List Integer -> IntPolynumber
    go _ [] = ZeroM
    go power (c :: cs) =
      if c == 0 then go (S power) cs
      else AddM (power, 0) c (go (S power) cs)

private
stripTrailingZeroes : List Integer -> List Integer
stripTrailingZeroes = reverse . dropWhile (== 0) . reverse

private
replicateNat : Nat -> a -> List a
replicateNat Z _ = []
replicateNat (S k) x = x :: replicateNat k x

private
safeLast : a -> List a -> a
safeLast def [] = def
safeLast _ [x] = x
safeLast def (x :: y :: ys) = safeLast def (y :: ys)

private
writeAt : Nat -> Integer -> List Integer -> List Integer
writeAt Z val [] = [val]
writeAt Z val (x :: xs) = val :: xs
writeAt (S k) val [] = 0 :: writeAt k val []
writeAt (S k) val (x :: xs) = x :: writeAt k val xs

private covering
polyDivLoop : List Integer -> List Integer -> List Integer -> Maybe (List Integer)
polyDivLoop aCoeffs bCoeffs qAcc =
  let aClean = stripTrailingZeroes aCoeffs in
  if null aClean then
    Just qAcc
  else
    let degA = cast (length aClean) - 1
        degB = cast (length bCoeffs) - 1
    in if degA < degB then
         Nothing
       else
         let leadA = safeLast 0 aClean
             leadB = safeLast 0 bCoeffs
         in if leadA `mod` leadB == 0 then
              let qCoeff = leadA `div` leadB
                  degDiff = degA - degB
                  degDiffNat = cast degDiff
                  subtractTerm = replicateNat degDiffNat 0 ++ map (* qCoeff) bCoeffs
                  padLength = max (length aClean) (length subtractTerm)
                  padA = aClean ++ replicateNat (minus padLength (length aClean)) 0
                  padSub = subtractTerm ++ replicateNat (minus padLength (length subtractTerm)) 0
                  aNext = zipWith (-) padA padSub
                  qNext = writeAt degDiffNat qCoeff qAcc
              in polyDivLoop aNext bCoeffs qNext
            else
              Nothing

private covering
polyDivExact : List Integer -> List Integer -> Maybe (List Integer)
polyDivExact a b =
  let a' = stripTrailingZeroes a
      b' = stripTrailingZeroes b
  in case b' of
       [] => Nothing
       bCoeffs => polyDivLoop a' bCoeffs []

private
natDivides : Nat -> Nat -> Bool
natDivides d' d =
  if d' == 0 then False
  else (cast d) `mod` (cast d') == 0

private
isProperDiv : Nat -> (d' : Nat ** IntPolynumber) -> Bool
isProperDiv d (d' ** _) =
  if d' `natDivides` d then
    case compare d' d of
      LT => True
      _  => False
  else
    False

||| Represents an exact primitive Integer Polynumber factor Ψ_d(x)
public export
data PrimitiveFactor : (d : Nat) -> Type where
  MkPrimitive : IntPolynumber -> PrimitiveFactor d

||| Computes the primitive factors for all divisors of n recursively.
export covering
gohFactorsForDivisors : (n : Nat) -> List (d : Nat ** IntPolynumber)
gohFactorsForDivisors Z = []
gohFactorsForDivisors n = go (divisors n) []
  where
    go : List Nat -> List (d : Nat ** IntPolynumber) -> List (d : Nat ** IntPolynumber)
    go [] acc = acc
    go (d :: ds) acc =
      let properDivs = filter (isProperDiv d) acc
          prodPoly = case properDivs of
                       [] => onePoly
                       ((_ ** p) :: ps) => foldl (\accP, (_ ** nextP) => mulIntPoly accP nextP) p ps
          sdPoly = spreadPoly d
          sdCoeffs = polyToCoeffs sdPoly
          pCoeffs = polyToCoeffs prodPoly
          psiCoeffs = case polyDivExact sdCoeffs pCoeffs of
                        Just q => q
                        Nothing => sdCoeffs
          psiPoly = coeffsToPoly psiCoeffs
          newAcc = acc ++ [(d ** psiPoly)]
      in go ds newAcc

||| The Goh Theorem implemented as a Type-Safe Factorisation Split.
||| Returns the list of primitive factors Ψ_d(s) indexed by the divisors d of n.
export covering
gohFactorise : (n : Nat) -> List (d : Nat ** PrimitiveFactor d)
gohFactorise n =
  let rawFactors = gohFactorsForDivisors n
  in map (\(d ** p) => (d ** MkPrimitive p)) rawFactors
