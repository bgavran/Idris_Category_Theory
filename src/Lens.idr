module Lens

import Category
import Monoidal

--record Comonoid where
--  constructor MkComonoid
--  mc : MonoidalCat
--  --c : obj (cat mc)
--  eta : {a : obj (cat mc)} -> hom (cat mc) a (unit mc) -- counit
--  delta : (a : obj (cat mc)) -> hom (cat mc) a (mapObj (x mc) (a, a))
  --copyDelete : {a : obj (cat mc)} ->
  --  o (cat mc) (mapMor (x mc) (a, a) ((unit mc), a) ?aaa)
  --  = idd (cat mc) {a=a}

-- record ComonoidHom (c1 : Comonoid) (c2 : Comonoid) where
--   constructor MkComonoidMor
--   --comFunctor : FFunctor (mc c1) (mc c2)

record Lens
  (lensCat : MonoidalCat)
  (i' : (obj (cat lensCat), obj (cat lensCat)))
  (o' : (obj (cat lensCat), obj (cat lensCat)))
    where
    constructor MkLens
    get : hom (cat lensCat) (fst i') (fst o')
    put : hom (cat lensCat) (mapObj (x lensCat) ((fst i'), (snd o'))) (fst o')


lensCompose : {mc : MonoidalCat} -> {a, b, c : (obj (cat mc), obj (cat mc))}
  -> Lens mc b c -> Lens mc a b -> Lens mc a c
lensCompose (MkLens g2 pu2) (MkLens g1 p1) = MkLens (o (cat mc) g2 g1) ?pp


--MkLens (g2 . g1) (\(a, z) => p1 a (p2 (g1 a) z))
--
--lensHom : (Type, Type) -> (Type, Type) -> Type
--lensHom (s, t) (a, b) = Lens s t a b
--

--lensCat mc = MkCat (Type, Type)  ?ee ?rr

idLens : {mc : MonoidalCat} -> {a : (obj (cat mc), obj (cat mc))}
  -> Lens mc a a
idLens = MkLens (idd (cat mc)) ?tt

lensCat : MonoidalCat -> Cat
lensCat mc = MkCat (obj (cat mc), (obj (cat mc))) (Lens mc) idLens lensCompose
