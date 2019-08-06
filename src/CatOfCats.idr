module CatOfCats

import Category
import Monoidal

categoryOfCategories : Cat
categoryOfCategories = MkCat Cat FFunctor idFunctor functorComposition

SingletonMorphism : () -> () -> Type
SingletonMorphism x y = () -> ()

categoryOneObject : Cat
categoryOneObject = MkCat () SingletonMorphism id (.)

--categoryOfCategoriesMonoidal : MonoidalCat
--categoryOfCategoriesMonoidal = MkMonoidalCat
--  categoryOfCategories
--  (MkFFunctor id ?rr)
--  categoryOneObject
--  ?aaaa
--  ?bbbb

dup : a -> (a, a)
dup a = (a, a)

-- Cat needs to be a comonoid?
--dupFunctor : FFunctor cat1 cat2 -> FFunctor (productCategory cat1 cat1) (productCategory cat2 cat2)
--dupFunctor (MkFFunctor o m) = MkFFunctor (dup o) ?bbb
