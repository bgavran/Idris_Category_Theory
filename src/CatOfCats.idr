module CatOfCats

import Category
import Monoidal
import Utils

catAssoc : {a, b, c, d : Cat}
  -> (f : FFunctor a b) -> (g : FFunctor b c) -> (h : FFunctor c d)
  -> functorComposition (functorComposition h g) f === functorComposition h (functorComposition g f)
catAssoc {a} {d} f g h = functorEq {cat1=a} {cat2=d}
  (functorComposition (functorComposition h g) f)
  (functorComposition h (functorComposition g f))
  (\x => Refl)
  (\x => Refl)

catRightId : {a, b : Cat}
  -> (f : FFunctor a b)
  -> idFunctor {cat=b} `functorComposition` f === f
catRightId f = functorEq {cat1=a} {cat2=b}
  (idFunctor {cat=b} `functorComposition` f)
  f
  (\x => Refl)
  (\x => Refl)

catLeftId : {a, b : Cat}
  -> (f : FFunctor a b)
  -> f `functorComposition` idFunctor {cat=a} === f
catLeftId f = functorEq
  (f `functorComposition` idFunctor {cat=a})
  f
  (\x => Refl)
  (\x => Refl)

categoryOfCategories : Cat
categoryOfCategories = MkCat
  Cat
  FFunctor
  idFunctor
  functorComposition
  catAssoc
  catLeftId
  catRightId

SingletonMorphism : () -> () -> Type
SingletonMorphism x y = () -> ()

categoryOneObject : Cat
categoryOneObject = MkCat
  ()
  SingletonMorphism
  id
  (.)
  (\_, _, _ => Refl)
  (\_ => Refl)
  (\_ => Refl)

categoryOfCategoriesMonoidal : MonoidalCat
categoryOfCategoriesMonoidal = MkMonoidalCat
  categoryOfCategories
  (MkFFunctor ?aaaa ?rrrr ?jjjj ?kkkk)
  categoryOneObject
  ?aaaaa
  ?bbbbb
  ?ccccc
