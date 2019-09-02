module MonoidalHelpers

import Category
import NaturalTransformation
import Product

public export
multiplyOnLeft : {c : Cat}
  -> (x : FFunctor (productCategory c c) c)
  -> (elem : obj c)
  -> FFunctor c c
multiplyOnLeft {c} x elem = MkFFunctor
  (\a => mapObj x (elem, a))
  (\f => mapMor x (MkProdMor (idd c {a=elem}) f))
  (\a => preserveId x (elem, a))
  (\ff, gg => let bnb = preserveComp x (MkProdMor ?zuz ?uiu) ?sss -- (MkProdMor (idd c) ?hhh) (MkProdMor (idd c) ?jjj)
              in ?xx)

public export
multiplyOnRight : {c : Cat} -> (x : FFunctor (productCategory c c) c) -> (elem : obj c) -> FFunctor c c
multiplyOnRight {c} x elem = MkFFunctor
  (\a => mapObj x (a, elem))
  (\f => mapMor x (MkProdMor f (idd c {a=elem})))
  (\a => preserveId x (a, elem))
  ?hjhj

public export
multiplyTwiceFromLeft : {c : Cat} -> FFunctor (productCategory c c) c -> FFunctor (productCategory (productCategory c c) c) c
multiplyTwiceFromLeft f =
  f `functorComposition`
  (productFunctor f idFunctor)

public export
multiplyTwiceAssociator : {c : Cat} -> FFunctor (productCategory c c) c -> FFunctor (productCategory (productCategory c c) c) c
multiplyTwiceAssociator f =
  (f `functorComposition`
    (productFunctor idFunctor f)) `functorComposition`
  productAssociator
