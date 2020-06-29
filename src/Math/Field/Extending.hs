{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, ScopedTypeVariables, EmptyDataDecls, FlexibleInstances #-}

module Math.Field.Extending where

import Prelude hiding ( (<*>) )

import Data.Ratio
import Data.List as L (elemIndex)

import Math.Common.IntegerAsType
import Math.Core.Utils
import Math.Algebra.Field.Base
import Math.Algebra.Field.Extension

data ConwayF256
instance PolynomialAsType F2 ConwayF256 where pvalue _ = convert $ x^8 + x^4 + x^3 + x^2 + 1
type F256 = ExtensionField F2 ConwayF256
f256 = map Ext (polys 8 f2) :: [F256]
a256 = embed x :: F256


data ConwayF512
instance PolynomialAsType F2 ConwayF512 where pvalue _ = convert $ x^9 + x^4 + 1
type F512 = ExtensionField F2 ConwayF512
f512 = map Ext (polys 9 f2) :: [F512]
a512 = embed x :: F512
