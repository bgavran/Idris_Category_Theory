module CatOfCats

import Category
import Monoidal

functorComposition : {cat1, cat2, cat3 : Cat} -> FFunctor cat2 cat3 -> FFunctor cat1 cat2 -> FFunctor cat1 cat3
functorComposition g@(MkFFunctor obc _) f@(MkFFunctor oab _) = MkFFunctor (obc . oab) (\a, b => (mapMor g (oab a) (oab b)) . (mapMor f a b))

categoryOfCategories : Cat
categoryOfCategories = MkCat Cat FFunctor idFunctor functorComposition

SingletonMorphism : () -> () -> Type
SingletonMorphism x y = () -> ()

categoryOneObject : Cat
categoryOneObject = MkCat () SingletonMorphism id (.)

categoryOfCategoriesMonoidal : MonoidalCat
categoryOfCategoriesMonoidal = MkMonoidalCat
  categoryOfCategories
  (MkFFunctor ?aa ?rr)
  categoryOneObject
  ?aaaa
  ?bbbb
