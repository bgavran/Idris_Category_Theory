module FunctorCategory

import Category
import NaturalTransformation
import Utils
--import Monoidal

assocNatTrans : (alpha : NatTrans c1 c2 f g)
  -> (beta : NatTrans c1 c2 g h)
  -> (gamma : NatTrans c1 c2 h i)
  -> compNatTrans (compNatTrans gamma beta) alpha === compNatTrans gamma (compNatTrans beta alpha)
assocNatTrans (MkNatTrans ff) (MkNatTrans gg) (MkNatTrans hh)
    = cong MkNatTrans $ let ww = funext (\a => ?ghg)
                        in ?assocNatTrans_rhs_2

leftIdNatTrans : (f : NatTrans c1 c2 a b) -> compNatTrans f idNatTrans === f
leftIdNatTrans (MkNatTrans ff) = ?leftIdNatTrans_rhs_1

functorCategory : Cat -> Cat -> Cat
functorCategory c1 c2 = MkCat
  (FFunctor c1 c2)
  (NatTrans c1 c2)
  idNatTrans
  compNatTrans
  assocNatTrans
  leftIdNatTrans
  ?rightIdNatTrans
