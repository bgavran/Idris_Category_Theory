module NaturalTransformation

import Category
import Utils

public export
record NatTrans
  (cat1 : Cat)
  (cat2 : Cat)
  (fun1 : FFunctor cat1 cat2)
  (fun2 : FFunctor cat1 cat2)
  where
    constructor MkNatTrans
    component : (a : obj cat1) -> hom cat2 (mapObj fun1 a) (mapObj fun2 a)
    naturality : {a, b : obj cat1} -> (f : hom cat1 a b)
      -> o cat2 {a=mapObj fun1 a} {b=mapObj fun1 b} {c=mapObj fun2 b}
        (component b)
        (mapMor fun1 {a=a} {b=b} f)
      === o cat2 {a=mapObj fun1 a} {b=mapObj fun2 a} {c=mapObj fun2 b}
        (mapMor fun2 {a=a} {b=b} f)
        (component a)

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
idNatTrans {cat2} = MkNatTrans
  (\a => idd cat2)
  (\ff => trans (rightId cat2 $ mapMor f1 ff) (sym $ leftId cat2 $ mapMor f1 ff))

public export
compNatTrans : {cat1, cat2 : Cat} -> {f1, f2, f3 : FFunctor cat1 cat2}
  -> NatTrans cat1 cat2 f2 f3
  -> NatTrans cat1 cat2 f1 f2
  -> NatTrans cat1 cat2 f1 f3
compNatTrans (MkNatTrans g pg) (MkNatTrans f pf) = MkNatTrans
  (\a => o cat2 (g a) (f a))
  (\ff => let ww = pg ff
              yy = pf ff
          in ?pgpf)


public export
assocNatTrans : {c1, c2 : Cat} -> {f, g, h, i : FFunctor c1 c2}
  -> (alpha : NatTrans c1 c2 f g)
  -> (beta :  NatTrans c1 c2   g h)
  -> (gamma : NatTrans c1 c2     h i)
  -> (gamma `compNatTrans` beta) `compNatTrans` alpha
  === gamma `compNatTrans` (beta `compNatTrans` alpha)
assocNatTrans {c1} {c2} {f} {i} alpha beta gamma
    = natTransEq c1 c2 f i
    ((gamma `compNatTrans` beta) `compNatTrans` alpha)
    (gamma `compNatTrans` (beta `compNatTrans` alpha))
    (\a => Refl)

public export
leftIdNatTrans : {c1, c2 : Cat} -> {a, b : FFunctor c1 c2}
  -> (f : NatTrans c1 c2 a b)
  -> f `compNatTrans` (idNatTrans {f1=a}) === f
leftIdNatTrans f = natTransEq c1 c2 a b
  (f `compNatTrans` (idNatTrans {f1=a}))
  f
  (\x => Refl)


public export
rightIdNatTrans : {c1, c2 : Cat} -> {a, b : FFunctor c1 c2}
  -> (f : NatTrans c1 c2 a b)
  -> (idNatTrans {f1=b}) `compNatTrans` f === f
rightIdNatTrans f = natTransEq c1 c2 a b
  ((idNatTrans {f1=b}) `compNatTrans` f)
  f
  (\x => Refl)

-- category whose objects are functors and maps are natural transformations
public export
functorCategory : Cat -> Cat -> Cat
functorCategory c1 c2 = MkCat
  (FFunctor c1 c2)
  (NatTrans c1 c2)
  idNatTrans
  compNatTrans
  assocNatTrans
  leftIdNatTrans
  rightIdNatTrans
