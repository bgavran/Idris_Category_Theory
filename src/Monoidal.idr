module Monoidal

import Category
import Product

%hide Prelude.(||) -- because I'm defining my custom || operator

public export
multiplyOnLeft : {c : Cat} -> (x : FFunctor (productCategory c c) c) -> (elem : obj c) -> FFunctor c c
multiplyOnLeft {c} x elem = MkFFunctor
  (\a => mapObj x (elem, a))
  (\f => mapMor x (MkProdMor (idd c {a=elem}) f))

public export
multiplyOnRight : {c : Cat} -> (x : FFunctor (productCategory c c) c) -> (elem : obj c) -> FFunctor c c
multiplyOnRight {c} x elem = MkFFunctor
  (\a => mapObj x (a, elem))
  (\f => mapMor x (MkProdMor f (idd c {a=elem})))

multiplyTwiceFromLeft : {c : Cat} -> FFunctor (productCategory c c) c -> FFunctor (productCategory (productCategory c c) c) c
multiplyTwiceFromLeft f =
  f `functorComposition`
  (productFunctor f idFunctor)

multiplyTwiceAssociator : {c : Cat} -> FFunctor (productCategory c c) c -> FFunctor (productCategory (productCategory c c) c) c
multiplyTwiceAssociator f =
  (f `functorComposition`
    (productFunctor idFunctor f)) `functorComposition`
  productAssociator


public export
record MonoidalCat where
  constructor MkMonoidalCat
  cat : Cat
  x : FFunctor (productCategory cat cat) cat
  unit : obj cat
  associator : NatIso (productCategory (productCategory cat cat) cat)
      cat (multiplyTwiceFromLeft x) (multiplyTwiceAssociator x)
  leftUnitor : NatIso cat cat (multiplyOnLeft x unit) (idFunctor {cat=cat})
  rightUnitor : NatIso cat cat (multiplyOnRight x unit) (idFunctor {cat=cat})

-- Monoidal product on objects
public export
(||) : {mcat : MonoidalCat}
  -> (a, b : obj (cat mcat)) -> obj (cat mcat)
(||) {mcat} a b = mapObj (x mcat) (a, b)


public export
record LaxMonoidalFunctor (cat1 : MonoidalCat) (cat2 : MonoidalCat) where
  constructor MkMonoidalFunctor
  ffunctor : FFunctor (cat cat1) (cat cat2)
  laxUnit : hom (cat cat2) (unit cat2) (mapObj ffunctor (unit cat1))
  --laxTensor : NatTrans (productCategory cat1 cat1) cat2

swapFunctor : FFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
swapFunctor = MkFFunctor (\o => (snd o, fst o)) (\(MkProdMor f g) => MkProdMor g f)
