package io.cosmo.exo.categories

import simulacrum.typeclass

@typeclass trait CategoryK[->[_[_], _[_]]] extends SemicategoryK[->] {
  type TC[f[_]]
  def id[F[_]](implicit A: TC[F]): F -> F
}
object CategoryK {
  trait Aux[->[_[_], _[_]], TC0[_[_]]] extends CategoryK[->] { type TC[A[_]] = TC0[A] }
  trait AuxT[->[_[_], _[_]]] extends Aux[->, Trivial.T2]
}
