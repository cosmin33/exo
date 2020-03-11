package io.cosmo.exo.categories

import io.cosmo.exo.evidence._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite

class CategoriesTests  extends AnyFunSuite with Matchers {

  val arr: Semicategory[Function] = implicitly[Semicategory[* => *]]

  implicitly[Subcat.Aux[* => *, Trivial.T1]]
  implicitly[Subcat[* => *]]

  implicitly[Subcat[Dual[* => *, *, *]]]

  implicitly[Subcat[Prodcat[* => *, * => *, *, *]]]
  implicitly[Subcat[Dicat[* => *, *, *]]]
  implicitly[Semicategory[Prodcat[* => *, * => *, *, *]]]
  implicitly[Ccc[Prodcat[* => *, * => *, *, *]]]
  implicitly[Distributive[Prodcat[* => *, * => *, *, *]]]
  implicitly[Cartesian[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Monoidal[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Symmetric[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Braided[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Associative[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Endobifunctor[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Groupoid[Prodcat[===, ===, *, *]]]


  def see1[->[_,_], C[_]](arr: ->[Int, Int])(implicit C: Subcat.Aux[->, C]) = C
  see1((i: Int) => i)


}
