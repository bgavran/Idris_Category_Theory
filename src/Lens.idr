module Lens

import Category
import NaturalTransformation
import Monoidal
import Product
import Comonoid
import Utils

%hide Prelude.(||)


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


--(mapObj
--    (functorComposition (x cc) (productFunctor (x cc) idFunctor))
--    ((a, b), c))
--(mapObj
--    (functorComposition
--        (functorComposition (x cc) (productFunctor idFunctor (x cc)))
--        productAssociator)
--    ((a, b), c))

--(mapObj (x cc) (mapObj (x cc) (a, b), c))     -- ((a || b) || c)
--(mapObj (x cc) (a, mapObj (x cc) (b, c)))     -- (a || (b || c))

composePut : (cmnd : Comonoid)
  -> (aa', bb', cc' : (obj (cat (mc cmnd)), obj (cat (mc cmnd))))
  -> hom (cat $ mc cmnd) (mapObj (x $ mc cmnd) (fst bb', snd cc')) (snd bb')
  -> hom (cat $ mc cmnd) (fst bb') (fst cc')
  -> hom (cat $ mc cmnd) (mapObj (x $ mc cmnd) (fst aa', snd bb')) (snd aa')
  -> hom (cat $ mc cmnd) (fst aa') (fst bb')
  -> hom (cat $ mc cmnd) (mapObj (x $ mc cmnd) (fst aa', snd cc')) (snd aa')
composePut cmnd (a, a') (b, b') (c, c') p2 g2 p1 g1
  = o (cat $ mc cmnd)
    (o (cat $ mc cmnd)
      (o (cat $ mc cmnd)
        p1
        (o (cat $ mc cmnd)
          (mapMor (x $ mc cmnd) {a=(a, (b, c'))} $ MkProdMor (idd $ cat $ mc cmnd) p2)
          ?composePutLast)
        )
      (mapMor (x $ mc cmnd) {a=((a, a), c')} {b=((a, b), c')}
        $ MkProdMor
          (mapMor (x $ mc cmnd) {b=(a, b)} $ MkProdMor (idd $ cat $ mc cmnd) g1)
          (idd $ cat $ mc cmnd)
      )
    )
    $ mapMor (x $ mc cmnd) {b=((a, a), c')} $ MkProdMor (copy cmnd) (idd $ cat $ mc cmnd)

lensCompose : {cmnd : Comonoid} -> {a, b, c : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))}
  -> Lens cmnd b c -> Lens cmnd a b -> Lens cmnd a c
lensCompose (MkLens g2 p2) (MkLens g1 p1) = MkLens
  (o (cat (mc cmnd)) g2 g1)
  (composePut cmnd a b c p2 g2 p1 g1)


idLens : {cmnd : Comonoid} -> {a : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))}
  -> Lens cmnd a a
idLens = MkLens
  (idd (cat (mc cmnd)))
  (projectSecond cmnd a)

lensLeftId : {cmnd : Comonoid} -> {a, b : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))}
  -> (f : Lens cmnd a b) -> f `lensCompose` (idLens {cmnd=cmnd}) === f
lensLeftId {cmnd} (MkLens get put) = cong2 MkLens
  (leftId (cat (mc cmnd)) get)
  ?lensLeftId_rhs_2

lensRightId : {cmnd : Comonoid} -> {a, b : (obj (cat (mc cmnd)), obj (cat (mc cmnd)))}
  -> (f : Lens cmnd a b) -> (idLens {cmnd=cmnd}) `lensCompose` f === f
lensRightId {cmnd} (MkLens get put) = cong2 MkLens
  (rightId (cat (mc cmnd)) get)
  ?lensRightId_rhs_2

lensCom : Comonoid -> Cat
lensCom cmnd = MkCat
  (obj (cat (mc cmnd)), (obj (cat (mc cmnd))))
  (Lens cmnd)
  idLens
  lensCompose
  ?lensAssoc
  lensLeftId
  lensRightId
