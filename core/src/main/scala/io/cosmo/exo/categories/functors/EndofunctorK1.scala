package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{CategoryK, Trivial}

trait EndofunctorK1[->[_[_],_[_]], A[_[_],_]] extends ExofunctorK1[->, ->, A] {
  override type TC2[f[_]] = TC1[f]
  override def D: CategoryK.Aux[->, TC2] = C
}
object EndofunctorK1 {
  trait Aux[->[_[_],_[_]], A[_[_],_], TC[_[_]]] extends EndofunctorK1[->, A] {
    type TC1[f[_]] = TC[f]
  }
  trait AuxT[->[_[_],_[_]], A[_[_],_]] extends EndofunctorK1.Aux[->, A, Trivial.T2]
}
