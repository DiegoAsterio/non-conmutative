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

-- -- |F256 is a type for the finite field with 256 elements.
-- -- F256 is represented as the extension of F2 by an element a256 satisfying x^8 + x^4 + x^3 + x^2 = 0
-- newtype F256 = F256 Int deriving (Eq,Ord)

-- instance Show F256 where
--     show (F256 0x0) = "0"
--     show (F256 0x1) = "1"
--     show (F256 0x10) = "a256"
--     show (F256 0x11) = "a256+1"
--     show (F256 0x100) = "a256^2"
--     show (F256 0x101) = "a256^2+1"
--     show (F256 0x110) = "a256^2+a256"
--     show (F256 0x111) = "a256^2+a256+1"
--     show (F256 0x1000) = "a256^3"
--     show (F256 0x1001) = "a256^3+1"
--     show (F256 0x1010) = "a256^3+a256"
--     show (F256 0x1011) = "a256^3+a256+1"
--     show (F256 0x1100) = "a256^3+a256^2"
--     show (F256 0x1101) = "a256^3+a256^2+1"
--     show (F256 0x1110) = "a256^3+a256^2+a256"
--     show (F256 0x1111) = "a256^3+a256^2+a256+1"
--     show (F256 0x10000) = "a256^4"
--     show (F256 0x10001) = "a256^4+1"
--     show (F256 0x10010) = "a256^4+a256"
--     show (F256 0x10011) = "a256^4+a256+1"
--     show (F256 0x10100) = "a256^4+a256^2"
--     show (F256 0x10101) = "a256^4+a256^2+1"
--     show (F256 0x10110) = "a256^4+a256^2+a256"
--     show (F256 0x10111) = "a256^4+a256^2+a256+1"
--     show (F256 0x11000) = "a256^4+a256^3"
--     show (F256 0x11001) = "a256^4+a256^3+1"
--     show (F256 0x11010) = "a256^4+a256^3+a256"
--     show (F256 0x11011) = "a256^4+a256^3+a256+1"
--     show (F256 0x11100) = "a256^4+a256^3+a256^2"
--     show (F256 0x11101) = "a256^4+a256^3+a256^2+1"
--     show (F256 0x11110) = "a256^4+a256^3+a256^2+a256"
--     show (F256 0x11111) = "a256^4+a256^3+a256^2+a256+1"
--     show (F256 0x100000) = "a256^5"
--     show (F256 0x100001) = "a256^5+1"
--     show (F256 0x100010) = "a256^5+a256"
--     show (F256 0x100011) = "a256^5+a256+1"
--     show (F256 0x100100) = "a256^5+a256^2"
--     show (F256 0x100101) = "a256^5+a256^2+1"
--     show (F256 0x100110) = "a256^5+a256^2+a256"
--     show (F256 0x100111) = "a256^5+a256^2+a256+1"
--     show (F256 0x101000) = "a256^5+a256^3"
--     show (F256 0x101001) = "a256^5+a256^3+1"
--     show (F256 0x101010) = "a256^5+a256^3+a256"
--     show (F256 0x101011) = "a256^5+a256^3+a256+1"
--     show (F256 0x101100) = "a256^5+a256^3+a256^2"
--     show (F256 0x101101) = "a256^5+a256^3+a256^2+1"
--     show (F256 0x101110) = "a256^5+a256^3+a256^2+a256"
--     show (F256 0x101111) = "a256^5+a256^3+a256^2+a256+1"

-- -- |a16 is a primitive element for F16 as an extension over F2. a16 satisfies x^4+x+1 = 0.
-- a16 :: F16
-- a16 = F16 0x10

-- instance Num F16 where
--     F16 x + F16 y = F16 $ (x+y) .&. 0x1111
--     negate x = x
--     F16 x * F16 y = F16 $ ((z654 `shiftR` 12) + (z654 `shiftR` 16) + z) .&. 0x1111
--         where z = x*y; z654 = z .&. 0xfff0000; -- z3210 = z .&. 0xffff
--         -- Explanation: We are making the substitution x^4 = x+1 (and also for x^5, x^6)
--     fromInteger n = F16 $ fromInteger n .&. 0x1
--     abs _ = error "Prelude.Num.abs: inappropriate abstraction"
--     signum _ = error "Prelude.Num.signum: inappropriate abstraction"

-- instance Fractional F16 where
--     recip (F256 0) = error "F16.recip 0"
--     recip x = x^14
--     fromRational _ = error "F16.fromRational: not well defined"

-- instance FinSet F16 where elts = f16

-- -- |f16 is a list of the elements of F16
-- f16 :: [F16]
-- f16 = L.sort $ 0 : powers a16
