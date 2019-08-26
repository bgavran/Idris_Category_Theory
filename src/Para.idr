module Para

import Category
import Monoidal

paraMorphism : (v : MonoidalCat) -> (a, b : (obj (cat v))) -> {p : obj (cat (v))} -> Type
paraMorphism v a b {p} = hom (cat v) (mapObj (x v) (p, a)) b

paraIdentityMap : (v : MonoidalCat)
  -> {a : obj (cat v)}
  -> hom (cat v) (mapObj (x v) (unit v, a)) a
paraIdentityMap = leftUnitorMap

para : MonoidalCat -> Cat
para v@(MkMonoidalCat cat x unit associator leftUnitor rightUnitor) =
  MkCat
  (obj cat)
  (\a, b => paraMorphism v a b) -- if I eta reduce I get type error?
  (let pim = paraIdentityMap v -- can't solve constraint ?p and unit?
   in ?ggg)
  ?para_rhs_4
  ?para_rhs_5
  ?para_rhs_6
  ?para_rhs_7
