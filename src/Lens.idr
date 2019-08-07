module Lens

import Category
import Monoidal

%hide Prelude.(||)

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
    put : hom (cat (mc lensCom)) (mapObj (x (mc lensCom)) ((fst i'), (snd o'))) (snd i')

composePut : (cmnd : Comonoid)
  -> (a, b, c : (obj (cat (mc cmnd)), obj (cat (mc cmnd))))
  -> hom (cat (mc cmnd)) (mapObj (x (mc cmnd)) (fst b, snd c)) (snd b)
  -> hom (cat (mc cmnd)) (fst b) (fst c)
  -> hom (cat (mc cmnd)) (mapObj (x (mc cmnd)) (fst a, snd b)) (snd a)
  -> hom (cat (mc cmnd)) (fst a) (fst b)
  -> hom (cat (mc cmnd)) (mapObj (x (mc cmnd)) (fst a, snd c)) (snd a)
composePut cmnd (a, a') (b, b') (c, c') p2 g2 p1 g1
  = o (cat (mc cmnd))
    ?zz
    (mapMor (x (mc cmnd)) {a=(a, c')} {b=(a || b, c')}
      (MkProdMor (o (cat (mc cmnd))
        (mapMor (x (mc cmnd)) (MkProdMor (idd (cat (mc cmnd)) {a=a}) g1))
        (copy cmnd)) (idd (cat (mc cmnd))))
      )


lensCompose : {cmnd : Comonoid} -> {a, b, c : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))}
  -> Lens cmnd b c -> Lens cmnd a b -> Lens cmnd a c
lensCompose (MkLens g2 p2) (MkLens g1 p1) = MkLens
  (o (cat (mc cmnd)) g2 g1)
  (composePut cmnd a b c p2 g2 p1 g1)


-- Given a x b,  this projects the second element by using comonoid delete
deleteSecond : (cmnd : Comonoid) -> (a : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))) -> hom (cat (mc cmnd)) (mapObj (x (mc cmnd)) (fst a, snd a)) (snd a)
deleteSecond cmnd a = let mm = component $ natTrans $ leftUnitor $ mc cmnd
                          pr = MkProdMor (delete cmnd) (idd (cat (mc cmnd)))
                      in o (cat (mc cmnd)) (mm $ snd a) (mapMor (x (mc cmnd)) {a=(fst a, snd a)} {b=(unit (mc cmnd), snd a)} pr)

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
