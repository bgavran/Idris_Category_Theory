module CatOfCats

import Category
import Monoidal

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
