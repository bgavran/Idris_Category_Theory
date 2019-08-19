module Comonoid

import Category
import Monoidal
import Product


-- Commutative
record Comonoid where
  constructor MkComonoid
  mc : MonoidalCat
  delete : {a : obj $ cat mc} -> hom (cat mc) a (unit mc)
  copy : {a : obj $ cat mc} -> hom (cat mc) a (mapObj (x mc) (a, a))
--  copyDeleteLaw : {a : obj (cat mc)}
--    -> o (cat mc) (mapMor (x mc) (a, a) ((unit mc), a) (MkProdMor (delete) (idd (cat mc)))) (copy) = idd (cat mc)
