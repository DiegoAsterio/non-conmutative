import Math.Algebras.VectorSpace
import Test.Hspec
import Test.QuickCheck
import Math.Field.Extending
import Math.NonConm.OrePolys
import Math.NonConm.OrePolys.TwistedPolys

main :: IO ()
main = hspec $ do
  describe "Twisted polynomial division" $ do
    it "qg + r  is always f where ldivQR f g = (q,r)" $ do
      property $ prop_ldivision
  describe "left extended euclidean algorithm, rgcd and llcm for twisted polynomials" $ do
    it "deg fg is always deg [f,g] + deg (f,g)" $ do
      property $ prop_lxea

-- TESTS

-- Testing properties on small examples 
-- To test properties on this polynomials first you need to generate random samples of this polynomials

-- Generate monomials
genMon :: Gen Monomial
genMon = M . ( abs <$>) <$> (arbitrary :: Gen (Maybe Int))

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
  (q,r) = ldivQR f g
  in case deg g of Just _ -> f == q*g + r
                   Nothing -> True

-- Testing if deg fg = deg [f,g] + deg (f,g) and if d right divides f and g
prop_lxea =
  forAll pairPolys $ \(f,g) -> let
  [d, alfa, alfa', beta, beta'] = lxea f g
  in case deg g of Nothing -> True
                   Just _ -> ldivq f d && ldivq g d && deg (f*g) == ((+) <$> (deg d) <*> (deg (alfa'*f)))

prop_llcm =
  forAll pairPolys $ \(f,g) -> let
  m = llcm f g
  [d, alfa, alfa', beta, beta'] = lxea f g
  in case deg g of Nothing -> True
                   Just _ -> alfa'*f == -beta'*g

prop_bound =
  forAll polys256 $ \f -> let
  fsharp = boundi (f :: TPF256P2)  (genMod f)
  in case deg f of Nothing -> True
                   Just _ -> (deg fsharp) <= ((*) <$> pure 4 <*> (deg f))
