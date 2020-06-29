{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, ScopedTypeVariables, FlexibleInstances #-}

module Math.NonConm.OrePolys.TwistedPolys where


import Math.Core.Field
import Math.Algebras.VectorSpace
import Lib
import Math.NonConm.OrePolys
import Math.Field.Extending

class OverFinFieldTP d poly where
  prim :: (d, poly) -> TwistedPoly d poly
  var :: (d, poly) -> TwistedPoly d poly
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
  t = var (undefined :: (d, poly))
  as = take deg $ iterate ((*) a) 1
  ts = take deg $ iterate ((*) t) 1
  in (*) <$> as <*> ts

data TwistedPolynomialF16P1
instance TwistedPolynomialAsType F16 TwistedPolynomialF16P1 where
  sigma _ = (\x -> x*x)
type TPF16P1 = TwistedPoly F16 TwistedPolynomialF16P1
instance OverFinFieldTP F16 TwistedPolynomialF16P1 where
  prim = (\_ -> fromd a16)
  var = (\_ -> TP $ V [(M (Just 1), 1)])
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
  var = (\_ -> TP $ V [(M (Just 1), 1)])
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
  var = (\_ -> TP $ V [(M (Just 1), 1)])
  powFie = (\_ -> 9)
  powFro = (\_ -> 3)

eg1 :: TPF512P3
eg1 = TP $ V [(M (Just 109), 1), (M (Just 79), a512^17), (M (Just 41), a512^37), (M (Just 17), a512^101), (M (Just 7), a512^271)]

-- embeddedCen ::
--   (Show d, Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly, OverFinFieldTP d poly) =>
--   TwistedPoly d poly ->
--   Unipol k
-- embeddedCen f = 

-- isIrred ::
--   (Show d, Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly, OverFinFieldTP d poly) =>
--   TwistedPoly d poly -> -- Polynomial f
--   Bool
-- isIrred (f :: TwistedPoly d poly) = let
--   s = sigma (undefined :: (d, poly))
--   mu = orderSigma f
--   t = var (undefined :: (d, poly))
--   divisibleByT = ldivq f t
--   cs = genMod f
--   bnd = boundi f cs
--   isIrredBnd = True
--   in not divisibleByT && deg bnd == ((*) <$> pure mu <*> deg f) && isIrredBnd

