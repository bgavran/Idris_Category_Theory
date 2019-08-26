module Monoidal

import Category
import NaturalTransformation
import Product
import MonoidalHelpers

%hide Prelude.(||) -- because I'm defining my custom || operator

public export
record MonoidalCat where
  constructor MkMonoidalCat
  cat : Cat
  x : FFunctor (productCategory cat cat) cat
  unit : obj cat
  associator : NatIso (productCategory (productCategory cat cat) cat) cat
    (multiplyTwiceFromLeft x) (multiplyTwiceAssociator x)
  leftUnitor : NatIso cat cat (multiplyOnLeft x unit) (idFunctor {cat=cat})
  rightUnitor : NatIso cat cat (multiplyOnRight x unit) (idFunctor {cat=cat})


associatorMap : (cc : MonoidalCat) -> (a, b, c : obj (cat cc))
   -> hom (cat cc) (mapObj (x cc) (mapObj (x cc) (a, b), c)) (mapObj (x cc) (a, mapObj (x cc) (b, c)))
associatorMap cc a b c = let zz = component (natTrans $ associator cc) ((a, b), c)
                         in ?zzz

--zz : hom (cat cc) (mapObj (x cc) (mapObj (productFunctor (x cc) (MkFFunctor AAA)) ((a, b), c)))
--                  (mapObj (x cc) (mapObj (productFunctor (MkFFunctor AAA) (x cc)) (a, (b, c))))
-----------           into          ----------------------------
--zz : hom (cat cc) (mapObj (x cc) (mapObj (x cc) (a, b), c))
--                  (mapObj (x cc) (a, mapObj (x cc) (b, c)))
--
--

--typeMonoidal : MonoidalCat
--typeMonoidal = MkMonoidalCat
--  typeCat
--  ?cartesianProdType
--  ()
--  ?typeMonoidald
--  ?typeMonoidale
--  ?typeMonoidalf

-- Monoidal product on objects
public export
(||) : {mcat : MonoidalCat}
  -> (a, b : obj (cat mcat)) -> obj (cat mcat)
(||) {mcat} a b = mapObj (x mcat) (a, b)


--public export
--record LaxMonoidalFunctor (cat1 : MonoidalCat) (cat2 : MonoidalCat) where
--  constructor MkMonoidalFunctor
--  ffunctor : FFunctor (cat cat1) (cat cat2)
--  laxUnit : hom (cat cat2) (unit cat2) (mapObj ffunctor (unit cat1))
  --laxTensor : NatTrans (productCategory cat1 cat1) cat2

swapFunctor : FFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
swapFunctor = MkFFunctor
  (\o => (snd o, fst o))
  (\(MkProdMor f g) => MkProdMor g f)
  ?vbvbv
  ?nmnm
