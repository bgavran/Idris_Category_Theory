module CatOfCats

import Category
import Monoidal

functorComposition : {cat1, cat2, cat3 : Cat} -> FFunctor cat2 cat3 -> FFunctor cat1 cat2 -> FFunctor cat1 cat3
functorComposition g@(MkFFunctor obc _) f@(MkFFunctor oab _)
  = MkFFunctor (obc . oab) (mapMor g . mapMor f)

categoryOfCategories : Cat
categoryOfCategories = MkCat
  Cat
  FFunctor
  idFunctor
  functorComposition
  ?catAssoc
  ?catLeftId
  ?catRightId

SingletonMorphism : () -> () -> Type
SingletonMorphism x y = () -> ()

categoryOneObject : Cat
categoryOneObject = MkCat () SingletonMorphism id (.) (\_, _, _ => Refl) (\_ => Refl) (\_ => Refl)

categoryOfCategoriesMonoidal : MonoidalCat
categoryOfCategoriesMonoidal = MkMonoidalCat
  categoryOfCategories
  (MkFFunctor ?aaaa ?rrrr)
  categoryOneObject
  ?aaaa
  ?bbbb
