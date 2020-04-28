package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.Endofunctor

trait Pointed[->[_,_], F[_]] extends Endofunctor[->, F] {
  def point[A]: A -> F[A]
}

object Pointed {
}
