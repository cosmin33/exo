package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

sealed abstract class TypeK[F[_]]

object TypeK {
  def apply[F[_]]: TypeK[F] = forall.apply[F]

  private[this] val forall: ∀~[TypeK] = ForallK.of[TypeK].fromH([T[_]] => () => new TypeK[T] {})

  given impl: ∀~[TypeK] = forall

  /** TypeF is injective, so if two TypeF's are equal then the types contained are equal. */
  def injectivity[F[_], G[_]](using TypeK[F] === TypeK[G]): F =~= G = Unsafe.isK[F, G]
  
  given isoTypeKInjectivity[F[_], G[_]]: ((TypeK[F] === TypeK[G]) <=> (F =~= G)) =
    Iso.unsafe(injectivity(using _), _.lower[TypeK])
}

sealed abstract class TypeK2[F[_, _]]

object TypeK2 {
//  def apply[F[_,_]]: TypeK2[F] = forall.apply[F]

//  private[this] val forall: ∀~~[TypeK2] = ForallK.of[TypeK2].fromH([T[_,_]] => () => new TypeK2[T] {})
//
//  given impl: ∀~~[TypeK2] = forall

//  /** TypeF is injective, so if two TypeF's are equal then the types contained are equal. */
//  def injectivity[F[_, _], G[_, _]](using TypeK2[F] === TypeK2[G]): F =~= G = Unsafe.isK2[F, G]
//
//  given isoTypeKInjectivity[F[_, _], G[_, _]]: ((TypeK2[F] === TypeK2[G]) <=> (F =~= G)) =
//    Iso.unsafe(injectivity(using _), _.lower[TypeK2])
}
