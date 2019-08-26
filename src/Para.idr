module Para

import Category
import Monoidal

paraMorphism : (v : MonoidalCat) -> (a, b : (obj (cat v))) -> {p : obj (cat (v))} -> Type
paraMorphism v a b {p} = hom (cat v) (mapObj (x v) (p, a)) b

public export
leftUnitorMap : (cc : MonoidalCat)
  -> {a : obj (cat (cc))}
  -> hom (cat cc) (mapObj (x cc) (unit cc, a)) a
leftUnitorMap cc {a} = component (natTrans $ leftUnitor cc) a


public export
paraIdentityMap : (v : MonoidalCat)
  -> {a : obj (cat v)}
  -> hom (cat v) (mapObj (x v) (unit v, a)) a
paraIdentityMap = leftUnitorMap

para : MonoidalCat -> Cat
para v@(MkMonoidalCat cat x unit associator leftUnitor rightUnitor) =
  MkCat
  (obj cat)
  (\a, b => paraMorphism v a b) -- if I eta reduce I get type error?
  ?para_rhs_3
  ?para_rhs_4
  ?para_rhs_5
  ?para_rhs_6
  ?para_rhs_7
