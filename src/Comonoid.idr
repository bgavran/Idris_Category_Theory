module Comonoid

import Category
import Monoidal
import Product


-- Comonoid on a SMC
record Comonoid where
  constructor MkComonoid
  mc : MonoidalCat
  delete : {a : obj $ cat mc} -> hom (cat mc) a (unit mc)
  copy : {a : obj $ cat mc} -> hom (cat mc) a (mapObj (x mc) (a, a))
  copyDeleteLaw : {a : obj $ cat mc}
    -> o (cat mc) {a=a} {b=(a,a)} {c=(unit mc, a)} (mapMor (x mc) {a=(a, a)} {b=(unit mc, a)} (MkProdMor (delete {a=a}) (idd (cat mc) {a=a}))) (copy {a=a}) ~=~ idd (cat mc) {a=a}

-- Given a x b,  this projects the second element by using comonoid delete
public export
projectSecond : (cmnd : Comonoid)
  -> (a : (obj (cat (mc cmnd)), obj (cat (mc cmnd))))
  -> hom (cat (mc cmnd)) (mapObj (x (mc cmnd)) (fst a, snd a)) (snd a)
projectSecond cmnd a = let mm = component $ natTrans $ leftUnitor $ mc cmnd
                           pr = MkProdMor (delete cmnd) (idd (cat (mc cmnd)))
                           morr = mapMor (x (mc cmnd)) {a=(fst a, snd a)} {b=(unit (mc cmnd), snd a)} pr
                       in o (cat (mc cmnd)) (mm $ snd a) morr
