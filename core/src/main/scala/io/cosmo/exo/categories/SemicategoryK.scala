package io.cosmo.exo.categories

import simulacrum.typeclass

@typeclass trait SemicategoryK[->[_[_], _[_]]] {
  def andThen[F[_], G[_], H[_]](ab: F -> G, bc: G -> H): F -> H
}
