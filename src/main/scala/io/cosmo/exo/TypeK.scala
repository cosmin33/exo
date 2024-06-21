package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

sealed abstract class TypeK[F[_]]

object TypeK {
  def apply[F[_]]: TypeK[F] = forall.apply[F]

  private[this] val forall: ∀~[TypeK] = ForallK.of[TypeK].fromH([T[_]] => () => new TypeK[T] {})

  given impl: ∀~[TypeK] = forall

  /** TypeK is injective, so if two TypeK's are equal then the types contained are equal. */
  def injectivity[F[_], G[_]](using TypeK[F] === TypeK[G]): F =~= G = Unsafe.isK[F, G]
  
  given isoTypeKInjectivity[F[_], G[_]]: ((TypeK[F] === TypeK[G]) <=> (F =~= G)) =
    Iso.unsafe(injectivity(using _), _.lower[TypeK])
}

sealed abstract class TypeK2[F[_,_]]

object TypeK2 {
  def apply[F[_,_]]: TypeK2[F] = forall.apply[F]

  private[this] val forall: ∀~~[TypeK2] = ForallK2.of[TypeK2].fromH([T[_,_]] => () => new TypeK2[T] {})

  given impl: ∀~~[TypeK2] = forall

  /** TypeK2 is injective, so if two TypeK2's are equal then the types contained are equal. */
  def injectivity[F[_,_], G[_,_]](using TypeK2[F] === TypeK2[G]): F =~~= G = Unsafe.isK2[F, G]

  given isoTypeKInjectivity[F[_,_], G[_,_]]: ((TypeK2[F] === TypeK2[G]) <=> (F =~~= G)) =
    Iso.unsafe(injectivity(using _), _.lower[TypeK2])
}

sealed abstract class TypeHK[A[_[_]]]

object TypeHK {
  def apply[A[_[_]]]: TypeHK[A] = forall.apply[A]

  private[this] val forall: ∀≈[TypeHK] = ForallHK.of[TypeHK].fromH([T[_[_]]] => () => new TypeHK[T] {})

  given impl: ∀≈[TypeHK] = forall

  /** TypeHK is injective, so if two TypeHK's are equal then the types contained are equal. */
  def injectivity[A[_[_]], B[_[_]]](using TypeHK[A] === TypeHK[B]): A =≈= B = Unsafe.isHK[A, B]

  given isoTypeHKInjectivity[A[_[_]], B[_[_]]]: ((TypeHK[A] === TypeHK[B]) <=> (A =≈= B)) =
    Iso.unsafe(injectivity(using _), _.lower[TypeHK])
}