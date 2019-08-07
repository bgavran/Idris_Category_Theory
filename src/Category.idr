module Category

import Utils

record Cat where
  constructor MkCat
  obj : Type
  hom : obj -> obj -> Type
  idd : {a : obj} -> hom a a
  o : {a, b, c : obj} -> hom b c -> hom a b -> hom a c
  assoc : {a, b, c, d : obj} -> (f : hom a b) -> (g : hom b c) -> (h : hom c d) ->
      (h `o` g) `o` f = h `o` (g `o` f)
  leftId : {a, b : obj} -> (f : hom a b) -> f `o` idd === f
  rightId : {a, b : obj} -> (f : hom a b) -> idd `o` f === f

TypeMorphism : Type -> Type -> Type
TypeMorphism a b = a -> b

typeCat : Cat
typeCat = MkCat Type TypeMorphism id (.) (\_, _, _ => Refl) (\_ => Refl) (\_ => Refl)

record ProdHom
  (cat1 : Cat)
  (cat2 : Cat)
  (a : (obj cat1, obj cat2))
  (b : (obj cat1, obj cat2))
  where
    constructor MkProdMor
    pi1 : hom cat1 (fst a) (fst b)
    pi2 : hom cat2 (snd a) (snd b)

prodComp : {cat1, cat2 : Cat} -> {a, b, c : (obj cat1, obj cat2)}
  -> ProdHom cat1 cat2 b c -> ProdHom cat1 cat2 a b -> ProdHom cat1 cat2 a c
prodComp (MkProdMor bcl bcr) (MkProdMor abl abr) = MkProdMor (o cat1 bcl abl) (o cat2 bcr abr)

prodAssoc : {cat1, cat2 : Cat} -> {a, b, c, d : (obj cat1, obj cat2)}
  -> (f : ProdHom cat1 cat2 a b)
  -> (g : ProdHom cat1 cat2 b c)
  -> (h : ProdHom cat1 cat2 c d)
  -> (h `prodComp` g) `prodComp` f = h `prodComp` (g `prodComp` f)
prodAssoc (MkProdMor f1 f2) (MkProdMor g1 g2) (MkProdMor h1 h2)
  = cong2 MkProdMor (assoc cat1 f1 g1 h1) (assoc cat2 f2 g2 h2)

prodLeftId : {cat1, cat2 : Cat}
  -> {a, b : (obj cat1, obj cat2)}
  -> (f : ProdHom cat1 cat2 a b)
  -> prodComp f (MkProdMor (idd cat1 {a=(fst a)}) (idd cat2 {a=(snd a)})) === f
prodLeftId (MkProdMor ll rr) = cong2 MkProdMor
  (leftId cat1 ll)
  (leftId cat2 rr)

prodRightId : {cat1, cat2 : Cat}
  -> {a, b : (obj cat1, obj cat2)}
  -> (f : ProdHom cat1 cat2 a b)
  -> prodComp (MkProdMor (idd cat1 {a=(fst b)}) (idd cat2 {a=(snd b)})) f === f
prodRightId (MkProdMor ll rr) = cong2 MkProdMor
  (rightId cat1 ll)
  (rightId cat2 rr)

productCategory : Cat -> Cat -> Cat
productCategory cat1 cat2 = MkCat
  (obj cat1, obj cat2)
  (ProdHom cat1 cat2)
  (MkProdMor (idd cat1) (idd cat2))
  prodComp
  prodAssoc
  prodLeftId
  prodRightId

-- FFunctor because it clashes with the name Functor in Idris
record FFunctor (cat1 : Cat) (cat2 : Cat) where
   constructor MkFFunctor
   mapObj : obj cat1 -> obj cat2
   mapMor : {a, b : obj cat1} -> hom cat1 a b -> hom cat2 (mapObj a) (mapObj b)
   --preserveIdentity : (a : obj cat1) -> (mapMor a a (idd cat1 {a})) = (idd cat2 {mapObj a})

idFunctor : {cat : Cat} -> FFunctor cat cat
idFunctor = MkFFunctor id id


productAssociator : FFunctor (productCategory (productCategory c1 c2) c3) (productCategory c1 (productCategory c2 c3))
productAssociator = MkFFunctor
  (\x => (fst (fst x), (snd (fst x), snd x)))
  (\f => MkProdMor (pi1 (pi1 f)) (MkProdMor (pi2 (pi1 f)) (pi2 f)))
-- if I pattern match here things break?
--(\((x, y), z) => (x, (y, z)))
--(\(MkProdMor (MkProdMor ll mm) rr) => (MkProdMor ?lll (MkProdMor ?mmm ?rrr)))

record Isomorphism (cat : Cat) (a : obj cat) (b : obj cat) (f : hom cat a b) where
  constructor MkIso
  inverse : hom cat b a

record NatTrans (cat1 : Cat) (cat2 : Cat) (f : FFunctor cat1 cat2) (g : FFunctor cat1 cat2) where
  constructor MkNatTrans
  component : (a : obj cat1) -> hom cat2 (mapObj f a) (mapObj g a)

record NatIso (cat1 : Cat) (cat2 : Cat) (f : FFunctor cat1 cat2) (g : FFunctor cat1 cat2) where
  constructor MkNatIso
  natTrans : NatTrans cat1 cat2 f g
  natIso : (a : obj cat1) -> Isomorphism cat2 (mapObj f a) (mapObj g a) (component natTrans a)
