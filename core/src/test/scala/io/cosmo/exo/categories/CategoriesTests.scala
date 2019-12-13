package io.cosmo.exo.categories

import io.cosmo.exo.categories.data.ProdCat
import io.cosmo.exo.evidence._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite

class CategoriesTests  extends AnyFunSuite with Matchers {

  val arr: Semicategory[Function] = implicitly[Semicategory[* => *]]

  implicitly[Subcat.Aux[Function1, Trivial.T1]]
  implicitly[Subcat[Function1]]

  implicitly[Subcat[Opp[Function1]#l]]

  implicitly[Subcat[ProdCat[Function1, Function1, *, *]]]

  def see1[->[_,_], C[_]](arr: ->[Int, Int])(implicit C: Subcat.Aux[->, C]) = C
  see1((i: Int) => i)


}
