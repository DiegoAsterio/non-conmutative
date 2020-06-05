{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, ScopedTypeVariables, FlexibleInstances #-}


module Math.NonConm.OrePolys where
import Prelude hiding ( (*>) )

-- Debuggers
import Debug.Trace
import Test.QuickCheck

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
  | otherwise = [c] ++ show n

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

-- instance Semigroup Monomial where
--   (<>) = mmult

-- instance Monoid Monomial where
--   mempty = unit

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
  AUT d ->
  TwistedPoly d poly -> --               First poly.
  TwistedPoly d poly -> --               Snd poly.
  (TwistedPoly d poly, TwistedPoly d poly) -- Result (q,r)
ldivQR s f g | deg f < deg g = (TP zerov, f)
             | otherwise = (l + quo, rem)
  where mon = mdiv (lm f) (lm g)
        s' = power s (mdeg mon)
        l = TP $ V $ [(mon, (lc f) * (recip (s' (lc g))))]
        l' = l * g
        f' = f - l'
        (quo, rem) = ldivQR s f' g

ldiv :: -- Left quotient of two polynomials
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  AUT d -> 
  TwistedPoly d poly -> -- Fst polynomial f
  TwistedPoly d poly -> -- Snd polynomial g
  TwistedPoly d poly --    Result: f /_l g
ldiv s f g = let (q,_) = ldivQR s f g
             in q

lrem :: -- Left remainder of two poly.
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  AUT d ->
  TwistedPoly d poly -> -- Fst polynomial f
  TwistedPoly d poly -> -- Snd polynomial g
  TwistedPoly d poly --    Result: f %_l g
lrem s f g = let (_,r) = ldivQR s f g
             in r

ldivq ::
  (Num d, Eq d, Fractional d, TwistedPolynomialAsType d poly) =>
  AUT d ->
  TwistedPoly d poly -> -- Fst polynomial f
  TwistedPoly d poly -> -- Snd polynomial g
  Bool --    Result: g | f ?
ldivq s f g = case deg $ lrem s f g of
  Nothing -> True
  Just _ -> False

lxea :: -- Left extended euclidean algorithm 
  (Eq d, Num d, Fractional d,TwistedPolynomialAsType d poly) =>
  AUT d -> --         the automorphism s;
  TwistedPoly d poly -> -- fst polynomial f;
  TwistedPoly d poly -> -- snd polynomial g;
  [TwistedPoly d poly] -- list including g.c.d.,
--                        bezout coeffs and more ...
--                        [d, s_n, s_n+1, t_n, t_n+1]
lxea s f g = lxea' f g onep zerop zerop onep
  where
    onep = fromd $ fromInteger 1
    zerop = TP $ zerov
    lxea' r0 r1 s0 s1 t0 t1 = case deg r1 of
      Nothing -> let invlc = recip $ lc r0
                     invlcpoly = fromd invlc
                 -- TODO: Make it an R-module
                 in ((*) invlcpoly) <$> [r0,s0,s1,t0,t1]
      Just _ -> let (q, r) = ldivQR s r0 r1
                    -- s_n+1 = s_n-1 - q_ns_n
                    s' = s0 - q*s1
                    -- t_n+1 = t_n-1 - q_nt_n
                    t' = t0 - q*t1 
                in lxea' r1 r s1 s' t1 t'
  
-- rgcd :: -- Calculate the right g.c.d.
--   (Eq k, Num k, Fractional k) =>
--   TwistedPolySigma k -> -- Fst. poly. f
--   TwistedPolySigma k -> -- Snd. poly. g
--   (TwistedPolySigma k, TwistedPolySigma k, TwistedPolySigma k) -- ((f,g)_r, s_n, t_n)
-- rgcd f g = let s = sigma f
--                fp = poly f
--                gp = poly g
--                d:alfa:beta:alfa':beta':[] = lxea s fp gp
--             in (TwistedPolySigma {poly = d, sigma = s},
--                 TwistedPolySigma {poly = alfa, sigma = s},
--                 TwistedPolySigma {poly = beta, sigma = s})

-- llcm :: -- Calculate the left l.c.m.
--   (Eq k, Num k, Fractional k) =>
--   TwistedPolySigma k -> -- Fst poly f
--   TwistedPolySigma k -> -- Snd poly g
--   TwistedPolySigma k --    [f,g]_l = s_n+1f = -t_n+1g

-- llcm f g = let s = sigma f
--                fp = poly f
--                gp = poly g
--                d:alfa:beta:alfa':beta':[] = lxea s fp gp
--                llcm = multP s alfa' fp
--            in TwistedPolySigma {poly = llcm, sigma = s}

-- annih :: -- Calculate the annihilator of an element h + Rf
--   (Eq k, Num k, Fractional k) =>
--   TwistedPolySigma k -> -- Polynomial f in the construction R/Rf
--   TwistedPolySigma k -> -- Polynomial h in R
--   TwistedPolySigma k -- Result: f_h such that f_hf = [f,h]_l
-- annih f h = let s = sigma f
--                 fp = poly f
--                 hp = poly h
--                 d:alfa:beta:alfa':beta':xs = lxea s fp hp
--                 annih' = beta'
--             in TwistedPolySigma {poly = annih', sigma = s}

-- boundi :: -- Calculate the bound of a polynomial f (i)
--   (Eq k, Num k, Fractional k) =>
--   TwistedPolySigma k -> -- Polynomial f
--   [TwistedPolySigma k] -> -- List of generators of R cs
--   TwistedPolySigma k -- Result: f^*
-- boundi f cs = foldr (\c g -> llcm (annih f c) g) f cs

-- boundii :: -- Calculate the bound of a polynomial f (ii)
--   (Show k, Eq k, Num k, Fractional k) =>
--   TwistedPolySigma k -> -- Polynomial f
--   [TwistedPolySigma k] -> -- List of generators of R ds
--   TwistedPolySigma k -- Result: f^*
-- boundii f ds = boundii' f ds
--   where boundii' g [] = g
--         boundii' g (di:dis) | trace ("boundii' g = " ++ show g ++ " di = " ++ show di) False = undefined 
--                             | (deg (lrem (multiplication g di) g)) == -1 = boundii' g  dis
--                             | otherwise = boundii' (llcm (annih g di) g) ds

-- EXAMPLES   

data TwistedPolynomialF16P1
instance TwistedPolynomialAsType F16 TwistedPolynomialF16P1 where
  sigma _ = (\x -> x*x)
type TPF16P1 = TwistedPoly F16 TwistedPolynomialF16P1

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

-- TESTS

-- Testing properties on small examples 
-- To test properties on this polynomials first you need to generate random samples of this polynomials

-- Generate monomials
genMon :: Gen Monomial
genMon = M <$> (arbitrary :: Gen (Maybe Int))

-- Generate elts. of the field F256
genF256 :: Gen F256
genF256 = (\x -> f256 !! (abs $ x `rem` 256)) <$> (arbitrary :: Gen Int)

-- Generate pairs of monomial element of F256
genMonF256 = (,) <$> genMon  <*> genF256

-- sized :: (Int -> Gen a) -> Gen a
poly256List :: Gen [(Monomial, F256)]
poly256List = sized $ \n ->
  frequency
    [ (1, return [])
    , (n, (:) <$> genMonF256 <*> poly256List)
    ]

-- Remove monomials == 0
remz :: [(Monomial,d)] -> [(Monomial,d)]
remz = filter (not . mzeroq . fst) 

-- Generate twisted. polynomial with D=256
polys256 = (TP . nf . V . remz) <$> poly256List

-- Generate a pair of polynomials
pairPolys :: Gen (TPF256P2, TPF256P2)
pairPolys = (,) <$> polys256 <*> polys256

-- Test if for q,r in eucl. alg. we have that f = qg + r
prop_ldivision =
   forAll pairPolys $ \(f,g) -> let
  (q,r) = ldivQR (\x -> x^4) f g
  in case deg g of Just _ -> f == q*g + r
                   Nothing -> True

-- Test if d left divides f and g
prop_lxea =
  forAll pairPolys $ \(f,g) -> let
  s = (\x -> x^4)
  [d, alfa, alfa', beta, beta'] = lxea s f g
  in case deg g of Nothing -> True
                   Just _ -> ldivq s f d && ldivq s g d






