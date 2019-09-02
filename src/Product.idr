module Product

import Category
import Utils

public export
record ProdHom
  (cat1 : Cat)
  (cat2 : Cat)
  (a : (obj cat1, obj cat2))
  (b : (obj cat1, obj cat2))
  where
    constructor MkProdMor
    pi1 : hom cat1 (fst a) (fst b)
    pi2 : hom cat2 (snd a) (snd b)

public export
prodComp : {cat1, cat2 : Cat} -> {a, b, c : (obj cat1, obj cat2)}
  -> ProdHom cat1 cat2   b c
  -> ProdHom cat1 cat2 a b
  -> ProdHom cat1 cat2 a   c
prodComp g f = MkProdMor (o cat1 (pi1 g) (pi1 f)) (o cat2 (pi2 g) (pi2 f))

public export
productId : {cat1, cat2 : Cat}
  -> {a : (obj cat1, obj cat2)}
  -> ProdHom cat1 cat2 a a
productId = MkProdMor
  (idd cat1 {a=(fst a)})
  (idd cat2 {a=(snd a)})

public export
prodAssoc : {cat1, cat2 : Cat} -> {a, b, c, d : (obj cat1, obj cat2)}
  -> (f : ProdHom cat1 cat2 a b)
  -> (g : ProdHom cat1 cat2 b c)
  -> (h : ProdHom cat1 cat2 c d)
  -> (h `prodComp` g) `prodComp` f = h `prodComp` (g `prodComp` f)
prodAssoc f g h = cong2 MkProdMor
  (assoc cat1 (pi1 f) (pi1 g) (pi1 h)) (assoc cat2 (pi2 f) (pi2 g) (pi2 h))

public export
prodLeftId : {cat1, cat2 : Cat}
  -> {a, b : (obj cat1, obj cat2)}
  -> (f : ProdHom cat1 cat2 a b)
  -> prodComp f (productId {a=(a, b)})  === f
prodLeftId (MkProdMor ll rr) = cong2 MkProdMor
  (leftId cat1 ll)
  (leftId cat2 rr)

public export
prodRightId : {cat1, cat2 : Cat}
  -> {a, b : (obj cat1, obj cat2)}
  -> (f : ProdHom cat1 cat2 a b)
  -> prodComp (productId {a=(a, b)}) f === f
prodRightId (MkProdMor ll rr) = cong2 MkProdMor
  (rightId cat1 ll)
  (rightId cat2 rr)

public export
productCategory : Cat -> Cat -> Cat
productCategory cat1 cat2 = MkCat
  (obj cat1, obj cat2)
  (ProdHom cat1 cat2)
  productId
  prodComp
  prodAssoc
  prodLeftId
  prodRightId

-- is this the correct to do this?
typeProductCat : Cat
typeProductCat = productCategory typeCat typeCat


public export
productAssociator : FFunctor
  (productCategory (productCategory c1 c2) c3)
  (productCategory c1 (productCategory c2 c3))
productAssociator = MkFFunctor
  (\x => (fst (fst x), (snd (fst x), snd x)))
  (\f => MkProdMor (pi1 (pi1 f)) (MkProdMor (pi2 (pi1 f)) (pi2 f)))
  (\a => Refl)
  (\ff, gg => trans ?dj ?fk)
  --(\ff, gg => cong2 MkProdMor ?prodAssocComp1 (cong2 MkProdMor ?prodAssocComp2 ?prodAssocComp3))




public export
productFunctor : FFunctor cat1 cat2 -> FFunctor cat3 cat4
  -> FFunctor (productCategory cat1 cat3) (productCategory cat2 cat4)
productFunctor f g = MkFFunctor
  (\x => (mapObj f (fst x), mapObj g (snd x)))
  (\ff => MkProdMor (mapMor f (pi1 ff)) (mapMor g (pi2 ff)))
  (\a => let zzzz = 1 -- this wont compile without the 'let'??
         in cong2 MkProdMor (preserveId f $ fst a) (preserveId g $ snd a))
  (\ff, gg => cong2 MkProdMor ?prodFunctComp1 ?prodFunctComp2)


swapFunctor : FFunctor (productCategory cat1 cat2) (productCategory cat2 cat1)
swapFunctor = MkFFunctor
  (\o => (snd o, fst o))
  (\f => MkProdMor (pi2 f) (pi1 f))
  (\_ => Refl)
  (\_, _ => Refl)
