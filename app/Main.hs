{-# LANGUAGE DataKinds, NoImplicitPrelude, OverloadedLabels #-}

module Main where

import qualified Prelude as P

import Algebra.Field.Galois
import Algebra.Prelude
import Algebra.Ring.Polynomial.Univariate
import Algebra.Ring.Polynomial.Factorise

import Math.Field.Extending
import Math.NonConm.OrePolys
import Math.NonConm.OrePolys.TwistedPolys

genField :: (Num a) => a ->
            Int ->
            [a]
genField gen n = 0:(take (n-1) (iterate ((P.*) gen) 1))

ds :: [F512]
ds = genField ((P.^) a512 73) 8

ds' :: [GF 2 3]
ds' = genField primitive 8

es :: [F256]
es = genField ((P.^) a256 85) 4

es' :: [GF 2 2]
es' = genField primitive 4

bnd = boundi eg1 (genMod eg1)

bndex215 = boundi ex215 (genMod ex215)

main :: IO ()
main = print $ embeddedCen es es' bndex215
           
