package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.CategoryK
import simulacrum.typeclass

trait ExofunctorK1[==>[_[_],_[_]], -->[_[_],_[_]], Trans[_[_],_]] {
  type TC1[_[_]]
  def C : CategoryK.Aux[==>, TC1]

  type TC2[_[_]]
  def D : CategoryK.Aux[-->, TC2]

  def mapK[F[_], G[_]](f: F ==> G): Trans[F, *] --> Trans[G, *]
}

object ExofunctorK1 {
  trait Aux[==>[_[_], _[_]], -->[_[_], _[_]], Alg[_[_],_], C1[_[_]], C2[_[_]]] extends ExofunctorK1[==>, -->, Alg] {
    type TC1[f[_]] = C1[f]
    type TC2[f[_]] = C2[f]
  }
}

trait ExofunctorK1Instances {

}