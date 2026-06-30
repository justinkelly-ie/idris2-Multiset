module Math.Maxel

import Math.Multiset
import public Math.Pixel

%default covering

||| A Maxel is a Multiset of Pixels, representing transition relations.
public export
0 Maxel : (metric : Metric) -> (c : Type) -> (a : Type) -> Type
Maxel metric c a = Multiset c (Pixel metric a)

||| Dynamic Maxel multiplication (Transitive Product).
||| Multiplies two Maxels element-wise. The product of [a,b] and [c,d] is Just [a,d] if b == c, and Nothing otherwise.
||| The result is a multiset of Maybe (Pixel a) entries, tracking unsuccessful annihilations as Nothing.
public export
mulMaxel : (Eq a, Num c, Eq c) => Maxel metric c a -> Maxel metric c a -> Multiset c (Maybe (Pixel metric a))
mulMaxel ZeroM _ = ZeroM
mulMaxel (AddM p1 c1 rest) m2 =
  addMultiset (mulInner p1 c1 m2) (mulMaxel rest m2)
  where
    mulInner : Pixel metric a -> c -> Maxel metric c a -> Multiset c (Maybe (Pixel metric a))
    mulInner _ _ ZeroM = ZeroM
    mulInner px cx (AddM py cy ys) =
      let pProd = mulPixel px py
          prodCount = cx * cy
      in insertItem pProd prodCount (mulInner px cx ys)

||| Takes the support of a multiplied Maxel.
||| Filters out all 'Nothing' entries (representing annihilated or non-transitive transitions),
||| returning a clean Maxel containing only the valid remaining transitions.
public export
supportMaxel : (Eq a, Num c, Eq c) => Multiset c (Maybe (Pixel metric a)) -> Maxel metric c a
supportMaxel ZeroM = ZeroM
supportMaxel (AddM Nothing c rest) = supportMaxel rest
supportMaxel (AddM (Just px) c rest) = AddM px c (supportMaxel rest)
