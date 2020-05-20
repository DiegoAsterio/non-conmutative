module Math.NonConm.OrePolys where
import Prelude hiding ( (*>) )

import Math.Core.Field
import Math.Algebras.VectorSpace

type AUT s = (s -> s)

newtype Monomial = M Int deriving (Eq, Ord)

showSummand :: Monomial -> String
showSummand (M n) | n == -1 = "0"
                  | n==0 = "1"
                  | n==1 = "T"
                  | otherwise = "T^" ++ show n

instance Show Monomial where
  show = showSummand

unit :: Monomial 
unit = M 0

mmult :: Monomial -> Monomial -> Monomial
mmult (M (-1)) _ = M (-1)
mmult _ (M (-1)) = M (-1)
mmult (M n) (M m) =  M (n+m)

mdivides :: Monomial -> Monomial -> Bool
mdivides (M m) (M n) = (m >= n)

mdiv :: Monomial -> Monomial -> Monomial
mdiv (M m) (M n) | mdivides (M m) (M n) = M (m-n)
                 | otherwise = error "Math.NonConm.OrePolys.mdiv: not divisible"

mdeg  :: Monomial -> Int
mdeg (M n) = n

instance Semigroup Monomial where
  (<>) = mmult

instance Monoid Monomial where
  mempty = unit
              
data TwistedPolySigma k = TwistedPolySigma { poly :: TwistedPoly k, sigma :: (AUT k) }

multiplyLists :: (Num k) => AUT k -> [(Monomial,k)] -> [(Monomial,k)] -> [(Monomial,k)]
multiplyLists s l1 l2 = (\(x1@(M n),k1) (x2,k2) -> (mmult x1 x2,k1*(iterate s k2 !! n))) <$> l1 <*> l2

multiplication :: (Num k, Eq k) => TwistedPolySigma k -> TwistedPolySigma k -> TwistedPolySigma k
multiplication f g = let V l1 = nf $ poly f
                         V l2 = nf $ poly g
                         s = sigma f
                     in TwistedPolySigma {poly= nf $ V $ multiplyLists s l1 l2, sigma=s}

addition :: (Num k, Eq k) => TwistedPolySigma k -> TwistedPolySigma k -> TwistedPolySigma k
addition f g = let s = sigma f
          in TwistedPolySigma {poly= poly f <+> poly g, sigma=s}

division :: (Num k, Eq k, Fractional k) => TwistedPolySigma k -> TwistedPolySigma k -> TwistedPolySigma k
division f g = let s = sigma f
                   fl = poly f
                   gl = poly g
               in TwistedPolySigma {poly = divideLists s fl gl, sigma=s}

degree :: (Eq k, Num k) => TwistedPoly k -> Int
degree f = let (V l1) = nf f
           in maximum $ map (mdeg . fst) l1

lt ::  (Eq k, Num k) => TwistedPoly k -> (Monomial, k)
lt f = let (V l) = nf f
       in head $ reverse l 

lm ::  (Eq k, Num k) => TwistedPoly k -> Monomial
lm = fst . lt

lc ::  (Eq k, Num k) => TwistedPoly k -> k
lc = snd . lt

power :: AUT k -> Int -> AUT k
power s n = (\x -> iterate s x !! n)

divideLists :: (Num k, Eq k, Fractional k) => AUT k -> TwistedPoly k -> TwistedPoly k -> TwistedPoly k
divideLists s f g | degree f < degree g = zerov
                  | otherwise = (V l) <+> divideLists s f' g
  where mon = mdiv (lm f) (lm g)
        s' = power s (degree f - degree g)
        V lg = g
        l = [(mon, (lc f) * (recip (s' (lc g))))]
        l' = multiplyLists s l lg
        f' = f <-> (V l')
                    
type TwistedPoly k = Vect k (Monomial)

instance (Show k, Eq k, Num k) => Show (TwistedPolySigma k) where
  show = show . poly

-- EXAMPLES   

frob = (\x -> x*x)

fl = V $ [(M 2, f16 !! 2), (M 1, f16 !! 10), (M 0, f16 !! 1)]
f = TwistedPolySigma {poly=fl, sigma=frob}

gl = V $ [(M 1, f16 !! 8), (M 0, f16 !!2)]
g = TwistedPolySigma {poly=gl, sigma=frob}

ql = V $ [(M 1, f16 !! 7), (M 0, f16 !! 6)]
q = TwistedPolySigma {poly=ql, sigma=frob}

rl = V $ [(M 0, f16 !! 13)]
r = TwistedPolySigma {poly=rl, sigma=frob}


-- data TwistedPoly k = TP [(k, Monomial)] (AUT k)

-- instance (Ord v) => Ord (OrePoly d v) where
--   compare (OP p) (Op q) = compare degp degq
--                           where degp = maximum $ map (\(x,y) -> deg y) p
