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
  associator : Isomorphism
    (functorCategory (productCategory (productCategory cat cat) cat) cat)
    (multiplyTwiceFromLeft x) (multiplyTwiceAssociator x)
  leftUnitor : Isomorphism
    (functorCategory cat cat)
    (multiplyOnLeft x unit) (idFunctor {cat=cat})
  rightUnitor : Isomorphism
    (functorCategory cat cat)
    (multiplyOnRight x unit) (idFunctor {cat=cat})
  -- TODO add coherence conditions

-- Monoidal product on objects
-- sometimes I can replace (mapMor (x mc) (a, b)) with (a || b) and the compiler
-- doesn't complain
public export
(||) : {mcat : MonoidalCat}
  -> (a, b : obj (cat mcat)) -> obj (cat mcat)
(||) {mcat} a b = mapObj (x mcat) (a, b)


swapThenMultiply : (mc : MonoidalCat)
  -> FFunctor (productCategory (cat mc) (cat mc)) (cat mc)
swapThenMultiply mc = (x mc) `functorComposition` swapFunctor

record SymmetricMonoidalCat (mc : MonoidalCat) where
  constructor MkSymmetricMonoidal
  swapMap : Isomorphism
    (functorCategory (productCategory (cat mc) (cat mc)) (cat mc))
    (x mc)
    (swapThenMultiply mc)
