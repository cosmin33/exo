package io.cosmo.exo.data

import io.cosmo.exo.evidence.{===, Is}

trait KleisModule {
  type Type[F[_], A, B] <: A => F[B]
  def leibniz[F[_], A, B]: Type[F, A, B] === (A => F[B])

}

private[exo] object KleisModuleImpl extends KleisModule {
  override type Type[F[_], A, B] = A => F[B]
  override def leibniz[F[_], A, B] = Is.refl
}
