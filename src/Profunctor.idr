module Profunctor

import Category
import Product
import NaturalTransformation

record Profunctor
  (v : Cat)
  (c : Cat)
  (d : Cat)
  where
    constructor MkProf
    prof : FFunctor (productCategory (dualCategory c) d) v

record ProfunctorMap
  (v : Cat)
  (c : Cat)
  (d : Cat)
  (p1 : Profunctor v c d)
  (p2 : Profunctor v c d)
  where
    constructor MkProfMap
    profMap : NatTrans (productCategory (dualCategory c) d) v (prof p1) (prof p2)

idProfunctorMap : {v, c, d : Cat} -> {a : Profunctor v c d}
  -> ProfunctorMap v c d a a
idProfunctorMap = MkProfMap idNatTrans

profunctorMapCompose : {v, c, d : Cat} -> {f, g, h : Profunctor v c d}
  -> ProfunctorMap v c d   g h
  -> ProfunctorMap v c d f g
  -> ProfunctorMap v c d f   h
profunctorMapCompose (MkProfMap profMap1) (MkProfMap profMap2) =
  MkProfMap $ compNatTrans profMap1 profMap2

profAssociativity : {v, c, d : Cat} -> {f, g, h, i : Profunctor v c d}
  -> (alpha : ProfunctorMap v c d f g)
  -> (beta :  ProfunctorMap v c d   g h)
  -> (gamma : ProfunctorMap v c d     h i)
  -> (gamma `profunctorMapCompose` beta) `profunctorMapCompose` alpha
  === gamma `profunctorMapCompose` (beta `profunctorMapCompose` alpha)
profAssociativity (MkProfMap profMap1) (MkProfMap profMap2) (MkProfMap profMap3)
  = cong MkProfMap $ let profAssociativity = (assocNatTrans profMap1 profMap2 profMap3)
                     in ?profAssociativityHole

leftIdProf : {v, c, d : Cat} -> {a, b : Profunctor v c d}
  -> (f : ProfunctorMap v c d a b)
  -> f `profunctorMapCompose` (idProfunctorMap {a=a}) === f
leftIdProf (MkProfMap profMap1)
  = cong MkProfMap $ let profLefId = leftIdNatTrans profMap1
                     in ?leftIdProf_rhs

rightIdProf : {v, c, d : Cat} -> {a, b : Profunctor v c d}
  -> (f : ProfunctorMap v c d a b)
  -> (idProfunctorMap {a=b}) `profunctorMapCompose` f === f
rightIdProf (MkProfMap profMap1)
  = cong MkProfMap $ let profLefId = rightIdNatTrans profMap1
                     in ?rightIdProf_rhs

-- objects are profunctors
categoryOfProfunctorMaps : (v, c, d : Cat) -> Cat
categoryOfProfunctorMaps v c d = MkCat
  (Profunctor v c d)
  (ProfunctorMap v c d)
  idProfunctorMap
  profunctorMapCompose
  profAssociativity
  leftIdProf
  rightIdProf
