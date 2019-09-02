module Category

import Utils


public export
record Cat where
  constructor MkCat
  obj : Type
  hom : obj -> obj -> Type
  idd : {a : obj} -> a `hom` a
  o : {a, b, c : obj}
    ->         b `hom` c
    -> a `hom` b
    -> a     `hom`     c
  assoc : {a, b, c, d : obj}
    -> (f : hom a b)
    -> (g : hom    b c)
    -> (h : hom      c d)
    -> (h `o`  g)`o` f
    === h `o` (g `o` f)
  leftId  : {a, b : obj} -> (f : hom a b) ->         f `o` idd === f
  rightId : {a, b : obj} -> (f : hom a b) -> idd `o` f         === f

TypeMorphism : Type -> Type -> Type
TypeMorphism a b = a -> b

public export
typeCat : Cat
typeCat = MkCat Type TypeMorphism id (.) (\_, _, _ => Refl) (\_ => Refl) (\_ => Refl)

-- FFunctor because it clashes with the name Functor in Idris
public export
record FFunctor (cat1 : Cat) (cat2 : Cat) where
   constructor MkFFunctor
   mapObj : obj cat1 -> obj cat2
   mapMor : {a, b : obj cat1} -> hom cat1 a b -> hom cat2 (mapObj a) (mapObj b)
   preserveId : (a : obj cat1) -> idd cat2 {a=(mapObj a)} === mapMor {a=a} {b=a} (idd cat1 {a=a})
   preserveComp : {a, b, c : obj cat1} -> (f : hom cat1 a b) -> (g : hom cat1 b c)
     -> mapMor {a=a} {b=c} (o cat1 {a=a} {b=b} {c=c} g f)
     === o cat2 {a=(mapObj a)} {b=(mapObj b)} {c=(mapObj c)} (mapMor {a=b} {b=c} g) (mapMor {a=a} {b=b} f)

public export
functorEq : {cat1, cat2 : Cat}
  -> (fun1, fun2 : FFunctor cat1 cat2)
  -> ((a : obj cat1) -> (mapObj fun1 a === mapObj fun2 a))
  -> ({a, b : obj cat1} -> (f : hom cat1 a b)
  -> (mapMor fun1 {a=a} {b=b} f ~=~ mapMor fun2 {a=a} {b=b} f))
  -> fun1 === fun2
functorEq fun1 fun2 f g = believe_me ()

public export
idFunctor : {cat : Cat} -> FFunctor cat cat
idFunctor = MkFFunctor id id (\_ => Refl) (\_, _ => Refl)


public export
functorComposition : {cat1, cat2, cat3 : Cat}
  -> FFunctor cat2 cat3
  -> FFunctor cat1 cat2
  -> FFunctor cat1 cat3
functorComposition g f = MkFFunctor
  (mapObj g . mapObj f)
  (mapMor g . mapMor f)
  (\a => trans (preserveId g $ mapObj f a) $ cong (mapMor g) $ preserveId f a)
  $ \fMor, gMor => trans
    (cong (mapMor g) $ preserveComp f fMor gMor)
    $ preserveComp g (mapMor f fMor) (mapMor f gMor)


public export
record Isomorphism (cat : Cat) (a : obj cat) (b : obj cat) where
  constructor MkIso
  forward : hom cat a b
  inverse : hom cat b a
  rightInverse : o cat {a=a} {b=b} {c=a}         inverse forward === idd cat {a=a}
  leftInverse  : o cat {a=b} {b=a} {c=b} forward inverse         === idd cat {a=b}

public export
dualCategory : Cat -> Cat
dualCategory c = MkCat
  (obj c)
  (flip $ hom c)
  (idd c)
  (flip $ o c)
  (\f, g, h => sym $ (assoc c) h g f)
  (rightId c)
  (leftId c)
