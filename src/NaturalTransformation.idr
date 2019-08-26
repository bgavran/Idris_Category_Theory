module NaturalTransformation

import Category

public export
record NatTrans (cat1 : Cat) (cat2 : Cat) (f : FFunctor cat1 cat2) (g : FFunctor cat1 cat2) where
  constructor MkNatTrans
  component : (a : obj cat1) -> hom cat2 (mapObj f a) (mapObj g a)


public export
natTransEq : (cat1, cat2 : Cat)
  -> (f, g : FFunctor cat1 cat2)
  -> (natTrans1, natTrans2 : NatTrans cat1 cat2 f g)
  -> ((a : obj cat1) -> (hom cat2 (mapObj f a) (mapObj g a) === hom cat2 (mapObj f a) (mapObj g a) ))
  -> natTrans1 === natTrans2
natTransEq cat1 cat2 f g natTrans1 natTrans2 f1 = believe_me ()


public export
idNatTrans : {cat1, cat2 : Cat} -> {f1 : FFunctor cat1 cat2}
  -> NatTrans cat1 cat2 f1 f1
idNatTrans {cat2} = MkNatTrans $ \a => idd cat2


-- this is eta reduction of two arguments?
applyDouble : (b -> b -> Type) -> (a -> b) -> (a -> b) -> (a -> a -> Type)
applyDouble f g h = \x => \y => f (g y) (g y)


public export
compNatTrans : {cat1, cat2 : Cat} -> {f1, f2, f3 : FFunctor cat1 cat2}
  -> NatTrans cat1 cat2 f2 f3
  -> NatTrans cat1 cat2 f1 f2
  -> NatTrans cat1 cat2 f1 f3
compNatTrans (MkNatTrans g) (MkNatTrans f)
  = MkNatTrans $ \a => o cat2 (g a) (f a)



public export
record NatIso (cat1 : Cat) (cat2 : Cat) (f : FFunctor cat1 cat2) (g : FFunctor cat1 cat2) where
  constructor MkNatIso
  natTrans : NatTrans cat1 cat2 f g
  natIso : (a : obj cat1) -> Isomorphism cat2 (mapObj f a) (mapObj g a) (component natTrans a)
