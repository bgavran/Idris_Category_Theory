module Test

import Category
import Monoidal

record Comonoid where
  constructor MkComonoid
  mc : MonoidalCat
  --c : obj (cat mc)
  eta : {a : obj (cat mc)} -> hom (cat mc) a (unit mc) -- counit
  delta : (a : obj (cat mc)) -> hom (cat mc) a (mapObj (x mc) (a, a))
  --copyDelete : {a : obj (cat mc)} ->
  --  o (cat mc) (mapMor (x mc) (a, a) ((unit mc), a) ?aaa)
  --  = idd (cat mc) {a=a}

record ComonoidHom (c1 : Comonoid) (c2 : Comonoid) where
  constructor MkComonoidMor
  --comFunctor : FFunctor (mc c1) (mc c2)

comonoidCategory : Cat
comonoidCategory = MkCat Comonoid ComonoidHom ?aa ?bb

record Lens s t a b where -- (c)   (c')
  constructor MkLens      -- (x)   (x')
  comonoidCat : Comonoid
  get : c -> c'
  put : (c, x') -> x

--
--lensCompose :  Lens a b c d -> Lens s t a b -> Lens s t c d
--lensCompose (MkLens get2 put2) (MkLens get1 put1) = MkLens (get2 . get1) (\(s, d) => put1 (s, put2 (get1 s, d)))
--
--lensHom : (Type, Type) -> (Type, Type) -> Type
--lensHom (s, t) (a, b) = Lens s t a b
--


--lensCat : Cat
--lensCat = MkCat (Type, Type) (\(s, t), (a, b) => Lens s t a b) (MkLens ?a ?b) ?cc
