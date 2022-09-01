package io.cosmo.exo.typeclasses

import io.cosmo.exo._
import io.cosmo.exo.evidence._
import io.cosmo.exo.evidence.internal.Unsafe

sealed abstract class TypeK[F[_]]

object TypeK {
  def apply[F[_]]: TypeK[F] = forall.apply[F]

  val forall: ForallK[TypeK] = ForallK.of[TypeK].fromH(f => new TypeK[f.T] {})

  implicit def impl: ForallK[TypeK] = forall

  /** TypeF is injective, so if two TypeF's are equal then the types contained are equal. */
  def injectivity[F[_], G[_]](implicit ev: TypeK[F] === TypeK[G]): F =~= G = Unsafe.isK[F, G]

  implicit def isoTypeKInjectivity[F[_], G[_]]: (TypeK[F] === TypeK[G]) <=> (F =~= G) =
    Iso.unsafe(injectivity(_), _.lower[TypeK])
}

