package io.cosmo.exo.categories

import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.evidence._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class CategoriesTests  extends AnyFunSuite with Matchers {

  val dd: Dual[* => *, Int, Int] = Dual((i: Int) => i * 2)
  val rr = dd.toFn

  // Prodcat
  implicitly[Semicategory[Prodcat[* => *, * => *, *, *]]]
  implicitly[Subcat[Prodcat[* => *, * => *, *, *]]]
  implicitly[Subcat.Aux[Prodcat[* => *, * => *, *, *], Trivial.T1]]
  implicitly[HasInitialObject[Prodcat[* => *, * => *, *, *]]]
  implicitly[HasInitialObject.Aux[Prodcat[* => *, * => *, *, *], Trivial.T1, Nothing]]
  implicitly[HasTerminalObject[Prodcat[* => *, * => *, *, *]]]
  implicitly[HasTerminalObject.Aux[Prodcat[* => *, * => *, *, *], Trivial.T1, Unit]]
  implicitly[Ccc[Prodcat[* => *, * => *, *, *]]]
  implicitly[Ccc.Aux[Prodcat[* => *, * => *, *, *], Trivial.T1, (*, *), Unit, * => *]]
  implicitly[Associative[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Associative.Aux[Prodcat[* => *, * => *, *, *], (*, *), Trivial.T1]]
  implicitly[Braided[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Braided.Aux[Prodcat[* => *, * => *, *, *], (*, *), Trivial.T1]]
  implicitly[Symmetric[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Symmetric.Aux[Prodcat[* => *, * => *, *, *], (*, *), Trivial.T1]]
  implicitly[Monoidal[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Monoidal.Aux[Prodcat[* => *, * => *, *, *], (*, *), Trivial.T1, Unit]]
  implicitly[Cartesian[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Cartesian.Aux[Prodcat[* => *, * => *, *, *], (*, *), Trivial.T1, Unit]]
  implicitly[Distributive[Prodcat[* => *, * => *, *, *]]]
  implicitly[Distributive.Aux[Prodcat[* => *, * => *, *, *], Trivial.T1, (*, *), Unit, Either, Nothing]]
  implicitly[Endobifunctor[Prodcat[* => *, * => *, *, *], (*, *)]]
  implicitly[Groupoid[Prodcat[===, ===, *, *]]]
  implicitly[Groupoid.Aux[Prodcat[===, ===, *, *], Trivial.T1]]

  def getDist[->[_,_], A, B, C[_], P[_,_], PI, S[_,_], SI](fn: A -> B)(implicit
    d: Distributive.Aux[->, C, P, PI, S, SI]
  ): Distributive.Aux[->, C, P, PI, S, SI] = d

  val fn = (i: Int) => i + 1
  val dd1 = getDist(fn)
  val ddd: Distributive.Aux[Function, T1, Tuple2, Unit, Either, Nothing] = getDist(fn)

  // Dual
  implicitly[Semicategory[Dual[* => *, *, *]]]
  implicitly[Subcat[Dual[* => *, *, *]]]
  implicitly[Endobifunctor[Dual[* => *, *, *], (*, *)]]
  implicitly[Associative[Dual[* => *, *, *], (*, *)]]
  implicitly[Braided[Dual[* => *, *, *], (*, *)]]
  implicitly[Symmetric[Dual[* => *, *, *], (*, *)]]
  implicitly[Monoidal[Dual[* => *, *, *], (*, *)]]

  // Dicat
  implicitly[Semicategory[Dicat[* => *, *, *]]]
  implicitly[Subcat[Dicat[* => *, *, *]]]
  implicitly[Endobifunctor[Dicat[* => *, *, *], (*, *)]]
  implicitly[Associative[Dicat[* => *, *, *], (*, *)]]
  implicitly[Braided[Dicat[* => *, *, *], (*, *)]]
  implicitly[Symmetric[Dicat[* => *, *, *], (*, *)]]
  implicitly[Monoidal[Dicat[* => *, *, *], (*, *)]]


  def see1[->[_,_], C[_]](arr: ->[Int, Int])(implicit C: Subcat.Aux[->, C]) = C
  see1((i: Int) => i)


}
