{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, ScopedTypeVariables, FlexibleInstances #-}


module Math.NonConm.OrePolys where
import Prelude hiding ( (*>) )

-- Debuggers
import Debug.Trace

import Algebra.Field.Galois
import qualified Algebra.Ring.Polynomial.Univariate as UP
import Algebra.Ring.Polynomial.Factorise

import Math.Core.Field
import Math.Algebras.VectorSpace

import Math.Field.Extending

type AUT s = (s -> s)

power :: -- calculate the power of an automorphism
  AUT k -> -- Automorphism s
  Int -> --   Integer n
  AUT k --    Result: s^n
power s n = (\x -> iterate s x !! n)

-- TODO: change monomial for Maybe Int
-- newtype Monomial = M Int deriving (Eq, Ord)
newtype Monomial = M (Maybe Int)
  deriving (Eq, Ord)

showMon :: Monomial -> String
showMon m = case m of
                M Nothing  -> "0"
                M (Just n) -> showVar 'T' n

showVar :: Char -> Int -> String
showVar c n
  | n==0 = "1"
  | n==1 = [c]
  | otherwise = [c] ++ "^" ++ show n

instance Show Monomial where
  show = showMon 

unit :: -- 1
  Monomial 
unit = M (Just 0)

mmult :: -- Monomial multiplication
  Monomial ->
  Monomial ->
  Monomial
mmult (M Nothing) _ = (M Nothing)
mmult _ (M Nothing) = (M Nothing)
mmult (M x) (M y) =  (M $ (+) <$> x <*> y)

mdivides :: -- Does a monomial divide another ?
  Monomial ->
  Monomial ->
  Bool
mdivides (M Nothing) _ = True
mdivides _ (M Nothing) = False
mdivides (M x) (M y) = case (>=) <$> x <*> y of
  Just x -> x
  Nothing -> error "Math.NonConm.OrePolys.mdivides: did not enter the correct branch of execution"

mdiv :: Monomial -> Monomial -> Monomial
mdiv mx@(M x) my@(M y)
  | mdivides mx my = (M $ (-) <$> x <*> y)
  | otherwise = error "Math.NonConm.OrePolys.mdiv: not divisible"

mdeg  :: -- Degree of a monomial
  Monomial ->
  Int
mdeg (M Nothing) = error "Math.NonConm.OrePolys.mdeg: degree -infty"
mdeg (M (Just m)) = m

mzeroq :: -- Is this the zero monomial
  Monomial ->
  Bool
mzeroq (M x) = case x of
  Nothing -> True
  Just _ -> False

class TwistedPolynomialAsType d poly where
-- sigma :: CAMBIAR ESTO ?? -> AUT d
  sigma :: (d,poly) -> AUT d
           
data TwistedPoly d poly = TP (Vect d (Monomial)) deriving (Eq, Ord)

instance (Show d, Eq d, Num d) => Show (TwistedPoly d poly) where
  show (TP f) = show f

multL :: -- Multiply two lists, each list represents a twisted polynomial
  (Num d) =>
  AUT d -> -- Automorphism s
  [(Monomial,d)] -> -- Fst polynomial f1
  [(Monomial,d)] -> -- Snd polynomial f2
  [(Monomial,d)] -- Result: f1*f2
multL s l1 l2 = filter (not . mzeroq . fst) $ f <$> l1 <*> l2
  where f (x1,k1) (x2,k2) = let s' = power s (mdeg x1)
                            in  (mmult x1 x2,k1*(s' k2))
                               
multP :: -- Multiply two twisted polynomials 
  (Num d, Eq d) =>
  AUT d -> -- Automorphism sigma 
  Vect d Monomial -> -- Fst polynomial f
  Vect d Monomial -> -- Snd polynomial g
  Vect d Monomial --    Result: f*g
multP s f g = let V l1 = nf f
                  V l2 = nf g
              in nf $ V $ multL s l1 l2

instance (Eq d, Fractional d, TwistedPolynomialAsType d poly) => Num (TwistedPoly d poly) where
  TP f + TP g = TP $ f <+> g
  TP f * TP g = let s = sigma (undefined :: (d,poly))
                in TP $ multP s f g
  negate (TP f) = TP $ negatev f
  fromInteger x = TP $ V [(M (Just 0), fromInteger x)]
  abs _ = error "Prelude.Num.abs: inappropriate abstraction"
  signum _ = error "Prelude.Num.signum: inappropiate abstraction" 

deg :: -- Deg of a polynomial
  (Eq d, Num d) =>
  TwistedPoly d poly -> -- Polynomial f
  Maybe Int --              Result: deg(f) = n
deg (TP f)= case nf f of V [] -> Nothing
                         V l1 -> Just $ maximum $ map (mdeg . fst) l1

lt :: -- leader term of a polynomial 
  (Eq d, Num d) =>
  TwistedPoly d poly -> -- Polynomial f
  (Monomial, d) --    Result: (M n, a_n)
lt (TP f) = let (V l) = nf f
            in head $ reverse l 

lm :: -- leader monomial of a polynomial
  (Eq d, Num d) =>
  TwistedPoly d poly -> -- Polynomial f 
  Monomial --         Result: M n
lm = fst . lt

lc :: -- leader coeff. of a polynomial
  (Eq d, Num d) =>
  TwistedPoly d poly -> -- Polynomial f
  d --                Result: a_n
lc = snd . lt

fromd ::
  (Eq d, Num d) =>
  d ->
  TwistedPoly d poly
fromd d = TP $ V [(M (Just 0), d)]

ldivQR :: -- Left divide two polynomials
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> --               First poly.
  TwistedPoly d poly -> --               Snd poly.
  (TwistedPoly d poly, TwistedPoly d poly) -- Result (q,r)
ldivQR f (g :: TwistedPoly d poly)
  | deg f < deg g = (TP zerov, f)
  | otherwise = (l + quo, rem)
  where
    s = sigma (undefined :: (d, poly))
    mon = mdiv (lm f) (lm g)
    s' = power s (mdeg mon)
    l = TP $ V $ [(mon, (lc f) * (recip (s' (lc g))))]
    l' = l * g
    f' = f - l'
    (quo, rem) = ldivQR f' g

ldiv :: -- Left quotient of two polynomials
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Fst polynomial f
  TwistedPoly d poly -> -- Snd polynomial g
  TwistedPoly d poly --    Result: f /_l g
ldiv f g = let (q,_) = ldivQR f g
             in q

lrem :: -- Left remainder of two poly.
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Fst polynomial f
  TwistedPoly d poly -> -- Snd polynomial g
  TwistedPoly d poly --    Result: f %_l g
lrem f g = let
  (_,r) = ldivQR f g
  in r

ldivq ::
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Fst polynomial f
  TwistedPoly d poly -> -- Snd polynomial g
  Bool --    Result: g | f ?
ldivq f g = case deg $ lrem f g of
  Nothing -> True
  Just _ -> False

monic :: -- Makes a polynomial monic
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly ->
  TwistedPoly d poly
monic f = let
  invlc = recip $ lc f
  invlcpoly = fromd invlc
  in invlcpoly * f

lxea :: -- Left extended euclidean algorithm 
  (Eq d, Num d, Fractional d,TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- fst polynomial f;
  TwistedPoly d poly -> -- snd polynomial g;
  [TwistedPoly d poly] -- list including g.c.d.,
--                        bezout coeffs and more ...
--                        [d, s_n, s_n+1, t_n, t_n+1]
lxea (f :: TwistedPoly d poly) g = lxea' f g onep zerop zerop onep
  where
    s = sigma (undefined :: (d, poly))
    onep = fromd $ fromInteger 1
    zerop = TP $ zerov
    lxea' r0 r1 s0 s1 t0 t1 = case deg r1 of
      Nothing -> let invlc = recip $ lc r0
                     invlcpoly = fromd invlc
                 -- TODO: Make it an R-module
                 in ((*) invlcpoly) <$> [r0,s0,s1,t0,t1]
      Just _ -> let (q, r) = ldivQR r0 r1
                    -- s_n+1 = s_n-1 - q_ns_n
                    s' = s0 - q*s1
                    -- t_n+1 = t_n-1 - q_nt_n
                    t' = t0 - q*t1 
                in lxea' r1 r s1 s' t1 t'
  
rgcd :: -- Calculate the right g.c.d.
  (Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Fst. poly. f
  TwistedPoly d poly -> -- Snd. poly. g
  [TwistedPoly d poly ] -- [(f,g)_r: s_n: t_n]
rgcd f g = let d:alfa:alfa':beta:beta':[] = lxea f g
             in [d, alfa, beta]

llcm :: -- Calculate the left l.c.m.
  (Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Fst poly f
  TwistedPoly d poly -> -- Snd poly g
  TwistedPoly d poly --    [f,g]_l = s_n+1f = -t_n+1g

llcm f g = let d:alfa:alfa':beta:beta':[] = lxea f g
             in alfa'*f

annih :: -- Calculate the annihilator of an element h + Rf
  (Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Polynomial f in the construction R/Rf
  TwistedPoly d poly -> -- Polynomial h in R
  TwistedPoly d poly -- Result: f_h such that f_hh = [f,h]_l
annih f h = let d:alfa:alfa':beta:beta':[] = lxea f h
            in -beta'

boundi :: -- Calculate the bound of a polynomial f (i)
  (Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Polynomial f
  [TwistedPoly d poly] -> -- List of generators of R cs
  TwistedPoly d poly -- Result: f^*
boundi f cs = monic $ foldr (\c g -> llcm (annih f c) g) f cs
                    

boundii :: -- Calculate the bound of a polynomial f (ii)
  (Show d, Eq d, Num d, Fractional d, TwistedPolynomialAsType d poly) =>
  TwistedPoly d poly -> -- Polynomial f
  [TwistedPoly d poly] -> -- List of generators of R ds
  TwistedPoly d poly -- Result: f^*
boundii f ds = monic $ boundii' f ds
  where boundii' g [] = g
        boundii' g (di:dis) = case (deg (lrem (g*di) g)) of Nothing -> boundii' g  dis
                                                            Just _ -> boundii' (llcm (annih g di) g) ds


