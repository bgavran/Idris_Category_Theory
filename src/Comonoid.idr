module Comonoid

import Category
import Monoidal
import Product
--import Para


-- Comonoid on a SMC
public export
record Comonoid where
  constructor MkComonoid
  mc : MonoidalCat
  delete : {a : obj $ cat mc} -> hom (cat mc) a (unit mc)
  copy : {a : obj $ cat mc} -> hom (cat mc) a (mapObj (x mc) (a, a))
  --copyDeleteLaw : {a : obj $ cat mc}
  --  -> o (cat mc) {a=a} {b=(unit mc, a)} {c=a}
  --    (leftUnitorMap mc {a=a})
  --    (o (cat mc) {a=a} {b=(a,a)} {c=(unit mc, a)}
  --      (mapMor (x mc) {a=(a, a)} {b=(unit mc, a)}
  --      (MkProdMor (delete {a=a}) (idd (cat mc) {a=a}))) (copy {a=a}))
  --  === idd (cat mc) {a=a}
  --assoc : {a : obj $ cat mc}
  --  -> o (cat mc) {a=a} {b=(a, a)} {c=((a, a), a)}
  --    (mapMor (x mc) {a=(a, a)} {b=((a, a), a)} (MkProdMor (copy {a=a}) (idd (cat mc) {a=a})))
  --    (copy {a=a})
  --  === o (cat mc) {a=a} {b=(a, a)} {c=(a, (a, a))}
  --    (mapMor (x mc) {a=(a, a)} {b=(a, (a, a))} (MkProdMor (idd (cat mc) {a=a}) (copy {a=a})))
  --    (copy {a=a})

-- Given a x b,  this projects the second element by using comonoid delete
public export
projectSecond : (cmnd : Comonoid)
  -> (a : (obj (cat (mc cmnd)), obj (cat (mc cmnd))))
  -> hom (cat (mc cmnd)) (mapObj (x (mc cmnd)) (fst a, snd a)) (snd a)
projectSecond cmnd a = let mm = component $ forward $ leftUnitor $ mc cmnd
                           pr = MkProdMor (delete cmnd) (idd (cat (mc cmnd)))
                           morr = mapMor (x (mc cmnd)) {a=(fst a, snd a)} {b=(unit (mc cmnd), snd a)} pr
                       in o (cat (mc cmnd)) (mm $ snd a) morr
