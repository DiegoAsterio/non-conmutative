{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, ScopedTypeVariables, FlexibleInstances, DataKinds, OverloadedLabels#-}

module Math.NonConm.OrePolys.TwistedPolys where

import qualified Numeric.Algebra as NA
import qualified Algebra.Prelude as AP

import Algebra.Ring.Polynomial.Univariate

import Math.Core.Field
import Math.Algebras.VectorSpace
import Lib
import Math.NonConm.OrePolys
import Math.Field.Extending
import Data.List as L

class OverFinFieldTP d poly where
  prim :: (d, poly) -> TwistedPoly d poly
  variable :: (d, poly) -> TwistedPoly d poly
  powFie :: (d, poly) -> Int
  powFro :: (d, poly) -> Int

orderSigma :: (Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly, OverFinFieldTP d poly) => TwistedPoly d poly -> Int
orderSigma (f :: TwistedPoly d poly) = let
  card = powFie (undefined :: (d, poly))
  k = powFro (undefined :: (d, poly))
  in card `div` (gcd card k)
  
genMod :: (Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly, OverFinFieldTP d poly) => TwistedPoly d poly -> [TwistedPoly d poly]
genMod (f :: TwistedPoly d poly) = let
  deg = orderSigma f
  a = prim (undefined :: (d, poly))
  t = variable (undefined :: (d, poly))
  as = take deg $ iterate ((*) a) 1
  ts = take deg $ iterate ((*) t) 1
  in (*) <$> as <*> ts

data TwistedPolynomialF16P1
instance TwistedPolynomialAsType F16 TwistedPolynomialF16P1 where
  sigma _ = (\x -> x*x)
type TPF16P1 = TwistedPoly F16 TwistedPolynomialF16P1
instance OverFinFieldTP F16 TwistedPolynomialF16P1 where
  prim = (\_ -> fromd a16)
  variable = (\_ -> TP $ V [(M (Just 1), 1)])
  powFie = (\_ -> 4)
  powFro = (\_ -> 1)


f :: TPF16P1
f = TP $ nf $ V $ [(M (Just 2), f16 !! 2), (M (Just 1), f16 !! 10), (M (Just 0), f16 !! 1)]

g :: TPF16P1
g = TP $ nf $ V $ [(M (Just 1), f16 !! 8), (M (Just 0), f16 !!2)]

q :: TPF16P1
q = TP $ nf $ V $ [(M (Just 1), f16 !! 7), (M (Just 0), f16 !! 6)]

r :: TPF16P1
r = TP $ nf $ V $ [(M (Just 0), f16 !! 13)]

data TwistedPolynomialF256P2
instance TwistedPolynomialAsType F256 TwistedPolynomialF256P2 where
  sigma _ = (\x -> x^4)
type TPF256P2 = TwistedPoly F256 TwistedPolynomialF256P2
instance OverFinFieldTP F256 TwistedPolynomialF256P2 where
  prim = (\_ -> fromd a256)
  variable = (\_ -> TP $ V [(M (Just 1), 1)])
  powFie = (\_ -> 8)
  powFro = (\_ -> 2)

ex215 :: TPF256P2
ex215 = TP $ nf $ V [(M (Just 100), 1), (M (Just 43), a256), (M (Just 20), a256^120), (M (Just 4), a256^35), (M (Just 0), a256^205)]


data TwistedPolynomialF512P3
instance TwistedPolynomialAsType F512 TwistedPolynomialF512P3 where
  sigma _ = (\x -> x^8)
type TPF512P3 = TwistedPoly F512 TwistedPolynomialF512P3
instance OverFinFieldTP F512 TwistedPolynomialF512P3 where
  prim = (\_ -> fromd a512)
  variable = (\_ -> TP $ V [(M (Just 1), 1)])
  powFie = (\_ -> 9)
  powFro = (\_ -> 3)

eg1 :: TPF512P3
eg1 = TP $ V [(M (Just 102), 1), (M (Just 72), a512^17), (M (Just 34), a512^37), (M (Just 10), a512^101), (M (Just 0), a512^271)]

polyToCoeffList :: (Eq d, Num d) =>
                   [d] ->
                   TwistedPoly d poly ->
                   Maybe [Int]
polyToCoeffList invs = sequence . (map (flip L.elemIndex invs)) . getCoeffs

fromCoeffList :: (Eq k, AP.FiniteField k, NA.Monoidal k) => [k] -> Unipol k
fromCoeffList = sum . zipWith (flip (AP..*.)) [ ( #x ^ n) | n <- [0 :: Int ..] ]

embeddedCen ::
  (AP.FiniteField k, Eq k, Show d, Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly, OverFinFieldTP d poly) =>
  [d] ->
  [k] ->
  TwistedPoly d poly ->
  Unipol k
embeddedCen ds ds' f = let degree = orderSigma f
                       in case polyToCoeffList ds f of Nothing -> error "Math.NonConm.OrePolys.TwistedPoly.embeddedCen: polynomial not in center"
                                                       Just l  -> fromCoeffList $ ((!!) ds') . snd <$> (filter (\(i,_) -> (i `rem` degree) == 0) $ zip [0..] l)

-- isIrred ::
--   (AP.FiniteField k, Eq k, Show d, Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly, OverFinFieldTP d poly) =>
--   [d] ->
--   [k] ->
--   TwistedPoly ds ds' d poly -> -- Polynomial f
--   Bool
-- isIrred (f :: TwistedPoly d poly) = let
--   s = sigma (undefined :: (d, poly))
--   mu = orderSigma f
--   t = variable (undefined :: (d, poly))
--   divisibleByT = ldivq f t
--   cs = genMod f
--   bnd = boundi f cs
--   bar = embeddedCen ds ds' bnd
--   isIrredBnd = factorise bar
--   in not divisibleByT && deg bnd == ((*) <$> pure mu <*> deg f) && isIrredBnd

