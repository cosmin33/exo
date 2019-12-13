package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories._
import simulacrum.typeclass

trait ExofunctorK[~~>[_[_],_[_]], |=>[_,_], Alg[_[_]]] {
  type TC1[_[_]]
  def C: CategoryK.Aux[~~>, TC1]

  type TC2[_]
  def D: Subcat.Aux[|=>, TC2]

  def mapK[F[_], G[_]](f: F ~~> G): Alg[F] |=> Alg[G]
}

object ExofunctorK {
  trait Aux[~>:[_[_], _[_]], =>:[_, _], Alg[_[_]], C1[_[_]], C2[_]] extends ExofunctorK[~>:, =>:, Alg] {
    type TC1[f[_]] = C1[f]
    type TC2[ᵒ] = C2[ᵒ]
  }
}