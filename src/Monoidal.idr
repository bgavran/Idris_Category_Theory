module Monoidal

import Category

%access public export
%default total

functorComposition : {cat1, cat2, cat3 : Cat} -> FFunctor cat2 cat3 -> FFunctor cat1 cat2 -> FFunctor cat1 cat3
functorComposition g@(MkFFunctor obc _) f@(MkFFunctor oab _) = MkFFunctor (obc . oab) (\a, b => (mapMor g (oab a) (oab b)) . (mapMor f a b))

-- Cat needs to be a comonoid?
--dupFunctor : FFunctor cat1 cat2 -> FFunctor (productCategory cat1 cat1) (productCategory cat2 cat2)
--dupFunctor (MkFFunctor o m) = MkFFunctor (dup o) ?bbb

multiplyOnLeft : {c : Cat} -> (x : FFunctor (productCategory c c) c) -> (elem : obj c) -> FFunctor c c
multiplyOnLeft {c} x elem = MkFFunctor (\a => mapObj x (elem, a)) (\a, b, f => mapMor x (elem, a) (elem, b) (MkProdMor (idd c) f))

multiplyOnRight : {c : Cat} -> (x : FFunctor (productCategory c c) c) -> (elem : obj c) -> FFunctor c c
multiplyOnRight {c} x elem = MkFFunctor (\a => mapObj x (a, elem)) (\a, b, f => mapMor x (a, elem) (b, elem) (MkProdMor f (idd c)))

record MonoidalCat where
  constructor MkMonoidalCat
  cat : Cat
  x : FFunctor (productCategory cat cat) cat
  unit : obj cat
  -- TODO add associator
  leftUnitor : NatIso cat cat (multiplyOnLeft x unit) (idFunctor {cat=cat})
  rightUnitor : NatIso cat cat (multiplyOnRight x unit) (idFunctor {cat=cat})

record LaxMonoidalFunctor (cat1 : MonoidalCat) (cat2 : MonoidalCat) where
  constructor MkMonoidalFunctor
  ffunctor : FFunctor (cat cat1) (cat cat2)
  laxUnit : hom (cat cat2) (unit cat2) (mapObj ffunctor (unit cat1))
  --laxTensor : NatTrans (productCategory cat1 cat1) cat2

swapFunctor : FFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
swapFunctor = MkFFunctor (\o => (snd o, fst o)) (\a, b, (MkProdMor f g) => MkProdMor g f)
