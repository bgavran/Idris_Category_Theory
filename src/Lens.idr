module Lens

import Category
import Monoidal

-- Commutative
record Comonoid where
  constructor MkComonoid
  mc : MonoidalCat
  delete : {a : obj (cat mc)} -> hom (cat mc) a (unit mc)
  copy : {a : obj (cat mc)} -> hom (cat mc) a (mapObj (x mc) (a, a))
--  copyDeleteLaw : {a : obj (cat mc)}
--    -> o (cat mc) (mapMor (x mc) (a, a) ((unit mc), a) (MkProdMor (delete) (idd (cat mc)))) (copy) = idd (cat mc)


-- s -> (a, b -> t)

||| Bimorphic lenses (called just lenses)
|||  (s)          (a)     get: s -> a
|||  ( )    ->    ( )
|||  (t)          (b)     put: s x b -> t
record Lens
  (lensCom : Comonoid)
  (i' : (obj (cat (mc lensCom)), obj (cat (mc lensCom))))
  (o' : (obj (cat (mc lensCom)), obj (cat (mc lensCom))))
    where
    constructor MkLens
    get : hom (cat (mc lensCom)) (fst i') (fst o')
    put : hom (cat (mc lensCom)) (mapObj (x (mc lensCom)) ((fst i'), (snd o'))) (fst o')


lensCompose : {cmnd : Comonoid} -> {a, b, c : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))}
  -> Lens cmnd b c -> Lens cmnd a b -> Lens cmnd a c
lensCompose (MkLens g2 pu2) (MkLens g1 p1) = MkLens (o (cat (mc cmnd)) g2 g1) ?pp


-- Given s x a,  this projects the first element by using comonoid delete
deleteSecond : (cmnd : Comonoid) -> (a : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))) -> hom (cat (mc cmnd)) (mapObj (x (mc cmnd)) (fst a, snd a)) (fst a)
deleteSecond cmnd a = let mm = component $ natTrans $ rightUnitor $ mc cmnd
                          pr = MkProdMor (idd (cat (mc cmnd))) (delete cmnd)
                      in o (cat (mc cmnd)) (mm $ fst a) (mapMor (x (mc cmnd)) (fst a, snd a) (fst a, unit (mc cmnd)) pr)

idLens : {cmnd : Comonoid} -> {a : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))}
  -> Lens cmnd a a
idLens = MkLens
  (idd (cat (mc cmnd)))
  (deleteSecond cmnd a)

lensCom : Comonoid -> Cat
lensCom cmnd = MkCat
  (obj (cat (mc cmnd)), (obj (cat (mc cmnd))))
  (Lens cmnd)
  idLens
  lensCompose
  ?lensAssoc
  ?lensLeftId
  ?lensRightId
