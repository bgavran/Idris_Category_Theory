module Category

import Utils


public export
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

-- FFunctor because it clashes with the name Functor in Idris
public export
record FFunctor (cat1 : Cat) (cat2 : Cat) where
   constructor MkFFunctor
   mapObj : obj cat1 -> obj cat2
   mapMor : {a, b : obj cat1} -> hom cat1 a b -> hom cat2 (mapObj a) (mapObj b)
   --preserveIdentity : (a : obj cat1) -> (mapMor a a (idd cat1 {a})) = (idd cat2 {mapObj a})

public export
idFunctor : {cat : Cat} -> FFunctor cat cat
idFunctor = MkFFunctor id id


public export
functorComposition : {cat1, cat2, cat3 : Cat} -> FFunctor cat2 cat3 -> FFunctor cat1 cat2 -> FFunctor cat1 cat3
functorComposition g@(MkFFunctor obc _) f@(MkFFunctor oab _)
  = MkFFunctor (obc . oab) (mapMor g . mapMor f)


public export
record Isomorphism (cat : Cat) (a : obj cat) (b : obj cat) (f : hom cat a b) where
  constructor MkIso
  inverse : hom cat b a

public export
record NatTrans (cat1 : Cat) (cat2 : Cat) (f : FFunctor cat1 cat2) (g : FFunctor cat1 cat2) where
  constructor MkNatTrans
  component : (a : obj cat1) -> hom cat2 (mapObj f a) (mapObj g a)

public export
record NatIso (cat1 : Cat) (cat2 : Cat) (f : FFunctor cat1 cat2) (g : FFunctor cat1 cat2) where
  constructor MkNatIso
  natTrans : NatTrans cat1 cat2 f g
  natIso : (a : obj cat1) -> Isomorphism cat2 (mapObj f a) (mapObj g a) (component natTrans a)
