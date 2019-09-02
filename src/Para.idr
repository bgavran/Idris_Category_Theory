module Para

import Category
import Monoidal

paraMorphism : (v : MonoidalCat)
  -> {p : obj (cat (v))}
  -> (a, b : (obj (cat v)))
  -> Type
paraMorphism v {p} a b = hom (cat v) (mapObj (x v) (p, a)) b

-- this function should not be here?
public export
leftUnitorMap : (cc : MonoidalCat)
  -> {a : obj $ cat $ cc}
  -> hom (cat cc) (mapObj (x cc) (unit cc, a)) a
leftUnitorMap cc {a} = component (forward $ leftUnitor cc) a

paraCompose : (mc : MonoidalCat)
  -> {a, b, c, p, q : obj $ cat mc}
  -> hom (cat mc) (mapObj (x mc) (q, b)) c
  -> hom (cat mc) (mapObj (x mc) (p, a)) b
  -> hom (cat mc) (mapObj (x mc) (mapObj (x mc) (p, q), a)) c

para : MonoidalCat -> Cat
para v = MkCat
  (obj $ cat v)
  (paraMorphism v)
  (leftUnitorMap v)
  --(paraCompose v)
  ?paraComposee
  ?para_rhs_5
  ?para_rhs_6
  ?para_rhs_7
