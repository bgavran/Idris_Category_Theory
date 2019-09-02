module Monoidal

import Category
import NaturalTransformation
import Product
import MonoidalHelpers
import Utils

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


-- basically I want to show there's a morphism ((A x B) x C) -> (A x (B x C))
public export
associatorMap : (cc : MonoidalCat) -> (a, b, c : obj (cat cc))
   -> hom (cat cc) (mapObj (x cc) (mapObj (x cc) (a, b), c)) (mapObj (x cc) (a, mapObj (x cc) (b, c)))
associatorMap cc a b c = component (natTrans $ associator cc) ((a, b), c)

-- Monoidal product on objects
public export
(||) : {mcat : MonoidalCat}
  -> (a, b : obj (cat mcat)) -> obj (cat mcat)
(||) {mcat} a b = mapObj (x mcat) (a, b)
