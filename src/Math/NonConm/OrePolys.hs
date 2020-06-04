{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables #-}


module Math.NonConm.OrePolys where
import Prelude hiding ( (*>) )

import Debug.Trace

import Math.Core.Field
import Math.Algebras.VectorSpace

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

showSummand :: Monomial -> String
showSummand m = case m of
                M Nothing  -> "0"
                M (Just n) -> showTs n

showTs :: Int -> String
showTs n
  | n==0 = "1"
  | n==1 = "T"
  | otherwise = "T^" ++ show n

instance Show Monomial where
  show = showSummand

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

multiplyLists :: -- Multiply two lists, each list represents a twisted polynomial
  (Num k) =>
  AUT k -> -- Automorphism s
  [(Monomial,k)] -> -- Fst polynomial f1
  [(Monomial,k)] -> -- Snd polynomial f2
  [(Monomial,k)] -- Result: f1*f2
multiplyLists s l1 l2 = f <$> l1 <*> l2
  where f (x1,k1) (x2,k2) = let s' = power s (mdeg x1)
                            in (mmult x1 x2,k1*(s' k2))
                               
multPoly :: -- Multiply two twisted polynomials 
  (Num d, Eq d) =>
  AUT d -> -- Automorphism sigma 
  Vect d Monomial -> -- Fst polynomial f
  Vect d Monomial -> -- Snd polynomial g
  Vect d Monomial --    Result: f*g
multPoly s f g = let V l1 = nf f
                     V l2 = nf g
                 in nf $ V $ multiplyLists s l1 l2

instance (Eq d, Fractional d, TwistedPolynomialAsType d poly) => Num (TwistedPoly d poly) where
  TP f + TP g = TP $ f <+> g
  TP f * TP g = let s = sigma (undefined :: (d,poly))
                in TP $ multPoly s f g
  negate (TP f) = TP $ negatev f
  fromInteger x = TP $ V [(M (Just 0), fromInteger x)]
  abs _ = error "Prelude.Num.abs: inappropriate abstraction"
  signum _ = error "Prelude.Num.signum: inappropiate abstraction" 

-- degreepoly :: -- Degree of a polynomial
--   (Eq k, Num k) =>
--   TwistedPoly k -> -- Polynomial f
--   Int --              Result: deg(f) = n
-- degreepoly f = case nf f of V [] -> -1
--                             V l1 -> maximum $ map (mdeg . fst) l1

-- degree :: -- Degree of a polynomial
--   (Eq k, Num k) =>
--   TwistedPolySigma k -> -- Polynomial f
--   Int --              Result: deg(f) = n
-- degree = degreepoly . poly

-- lt :: -- leader term of a polynomial 
--   (Eq k, Num k) =>
--   TwistedPoly k -> -- Polynomial f
--   (Monomial, k) --    Result: (M n, a_n)
-- lt f = let (V l) = nf f
--        in head $ reverse l 

-- lm :: -- leader monomial of a polynomial
--  (Eq k, Num k) =>
--  TwistedPoly k -> -- Polynomial f 
--  Monomial --         Result: M n
-- lm = fst . lt

-- lc :: -- leader coeff. of a polynomial
--   (Eq k, Num k) =>
--   TwistedPoly k -> -- Polynomial f
--   k --                Result: a_n
-- lc = snd . lt

-- lDividePolyQuoRem :: -- Left divide two polynomials
--   (Num k, Eq k, Fractional k) =>
--   AUT k -> --                       Automorphism s
--   TwistedPoly k -> --               First poly.
--   TwistedPoly k -> --               Snd poly.
--   (TwistedPoly k, TwistedPoly k) -- Result (q,r)
-- lDividePolyQuoRem s f g | degreepoly f < degreepoly g = (zerov, f)
--                         | otherwise = ((V l) <+> quo, rem)
--   where mon = mdiv (lm f) (lm g)
--         s' = power s (mdeg mon)
--         l = [(mon, (lc f) * (recip (s' (lc g))))]
--         V lg = g
--         l' = multiplyLists s l lg
--         f' = f <-> (V l')
--         (quo, rem) = lDividePolyQuoRem s f' g

-- lDivideQuo :: -- Left quotient of two polynomials
--   (Num k, Eq k, Fractional k) =>
--   TwistedPolySigma k -> -- Fst polynomial f
--   TwistedPolySigma k -> -- Snd polynomial g
--   TwistedPolySigma k --    Result: f/g
-- lDivideQuo f g = let s = sigma f
--                      fl = poly f
--                      gl = poly g
--                  in TwistedPolySigma {poly = fst $ lDividePolyQuoRem s fl gl, sigma=s}

-- lDivideRem :: -- Left remainder of the two poly.
--   (Num k, Eq k, Fractional k) =>
--   TwistedPolySigma k -> -- Fst polynomial f
--   TwistedPolySigma k -> -- Snd polynomial g
--   TwistedPolySigma k --    Result: f%g
-- lDivideRem f g = let s = sigma f
--                      fl = poly f
--                      gl = poly g
--                  in TwistedPolySigma {poly = snd $ lDividePolyQuoRem s fl gl, sigma=s}

-- lxea :: -- Left extended euclidean algorithm 
--   (Eq k, Num k, Fractional k) =>
--   AUT k -> --         the automorphism s;
--   TwistedPoly k -> -- fst polynomial f;
--   TwistedPoly k -> -- snd polynomial g;
--   [TwistedPoly k] --  list including g.c.d.,
-- --                    bezout coeffs and more ...
-- --                    (d, s_n, s_n+1, t_n, t_n+1)
-- lxea s f g = lxea' f g onep zerov zerov onep
--   where
--     onep = (V [(M 0, 1)])
--     lxea' r0 r1 s0 s1 t0 t1 | degreepoly r1 == -1 =
--                                 let invlc = recip $ lc r0
--                                 in ((*>) invlc) <$> [r0,s0,s1,t0,t1]
--                             | otherwise =
--                                 let (q, r) = lDividePolyQuoRem s r0 r1
--                                     -- s_n+1 = s_n-1 - q_ns_n
--                                     s' = s0 <-> multPoly s q s1
--                                     -- t_n+1 = t_n-1 - q_nt_n
--                                     t' = t0 <-> multPoly s q t1 
--                                 in lxea' r1 r s1 s' t1 t'
  
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
--                llcm = multPoly s alfa' fp
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
--                             | (degree (lDivideRem (multiplication g di) g)) == -1 = boundii' g  dis
--                             | otherwise = boundii' (llcm (annih g di) g) ds

-- -- EXAMPLES   

-- frob = (\x -> x*x)

-- fl = V $ [(M 2, f16 !! 2), (M 1, f16 !! 10), (M 0, f16 !! 1)]
-- f = TwistedPolySigma {poly=fl, sigma=frob}

-- gl = V $ [(M 1, f16 !! 8), (M 0, f16 !!2)]
-- g = TwistedPolySigma {poly=gl, sigma=frob}

-- ql = V $ [(M 1, f16 !! 7), (M 0, f16 !! 6)]
-- q = TwistedPolySigma {poly=ql, sigma=frob}

-- rl = V $ [(M 0, f16 !! 13)]
-- r = TwistedPolySigma {poly=rl, sigma=frob}


