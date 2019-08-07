module Monoidal

import Category

%hide Prelude.(||) -- because I'm defining my custom || operator

multiplyOnLeft : {c : Cat} -> (x : FFunctor (productCategory c c) c) -> (elem : obj c) -> FFunctor c c
multiplyOnLeft {c} x elem = MkFFunctor
  (\a => mapObj x (elem, a))
  (\f => mapMor x (MkProdMor (idd c {a=elem}) f))

multiplyOnRight : {c : Cat} -> (x : FFunctor (productCategory c c) c) -> (elem : obj c) -> FFunctor c c
multiplyOnRight {c} x elem = MkFFunctor
  (\a => mapObj x (a, elem))
  (\f => mapMor x (MkProdMor f (idd c {a=elem})))

record MonoidalCat where
  constructor MkMonoidalCat
  cat : Cat
  x : FFunctor (productCategory cat cat) cat
  unit : obj cat
  -- TODO add associator
  leftUnitor : NatIso cat cat (multiplyOnLeft x unit) (idFunctor {cat=cat})
  rightUnitor : NatIso cat cat (multiplyOnRight x unit) (idFunctor {cat=cat})

-- Monoidal product on objects
(||) : {mcat : MonoidalCat}
  -> (a, b : obj (cat mcat)) -> obj (cat mcat)
(||) {mcat} a b = mapObj (x mcat) (a, b)

record LaxMonoidalFunctor (cat1 : MonoidalCat) (cat2 : MonoidalCat) where
  constructor MkMonoidalFunctor
  ffunctor : FFunctor (cat cat1) (cat cat2)
  laxUnit : hom (cat cat2) (unit cat2) (mapObj ffunctor (unit cat1))
  --laxTensor : NatTrans (productCategory cat1 cat1) cat2

swapFunctor : FFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
swapFunctor = MkFFunctor (\o => (snd o, fst o)) (\(MkProdMor f g) => MkProdMor g f)
