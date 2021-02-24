package io.cosmo.exo.evidence.variance

import io.cosmo.exo._
import io.cosmo.exo.evidence._
import cats.implicits._
import io.cosmo.exo.categories.Dual
import io.cosmo.exo.categories.functors.Exo

trait IsContravariant[F[_]] { F =>

  def apply[A, B](implicit ab: A <~< B): F[B] <~< F[A]

  def substCo[G[+_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    F(ev).substCv[G](g)

  def substCt[G[-_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    F(ev).substCt[G](g)

  def coerce[A, B](value: F[B])(implicit ev: A <~< B): F[A] =
    F(ev).coerce(value)

  def widen[A, B](fa: F[B])(implicit ev: A <~< B): F[A] =
    F(ev).apply(fa)

  def composeCo[G[_]](G: IsCovariant[G]): IsContravariant[λ[x => F[G[x]]]] =
    IsContravariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composeCt[G[_]](G: IsContravariant[G]): IsCovariant[λ[x => F[G[x]]]] =
    IsCovariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composePh[G[_]](G: IsConstant[G]): IsConstant[λ[x => F[G[x]]]] =
    G.andThenCt[F](F)
}
object IsContravariant {
  type Canonic[F[_]] = ∀∀[λ[(a,b) => (a <~< b) => F[b] <~< F[a]]]
  def apply[F[_]](implicit ev: IsContravariant[F]): IsContravariant[F] = ev

  def witness[F[_]](fba: F[Any] <~< F[Void]): IsContravariant[F] =
    witness1[F, Void, Any](StrictAs.bottomTop, fba)

  def witness1[F[_], A, B](implicit ab: A </< B, fba: F[B] <~< F[A]): IsContravariant[F] =
    new IsContravariant[F] {
      override def apply[X, Y](implicit xy: X <~< Y): F[Y] <~< F[X] =
        Is.lem[X, Y].map {
          _.fold(
            neqv => Parametric[F].liftCt[A, B, X, Y](ab, fba, StrictAs.witness(neqv, xy)),
            eqv => eqv.lift[F].flip.toAs
          )
        }.proved
    }

  def witness1[F[_]](implicit ev: F[Any] <~< F[Void]): IsContravariant[F] =
    witness[F](ev)

  implicit def reify[F[-_]]: IsContravariant[F] =
    witness[F](As.reify[F[Any], F[Void]])

  implicit def proposition[F[_]]: Proposition[IsContravariant[F]] =
    (A: ¬¬[IsContravariant[F]]) => new IsContravariant[F] {
      override def apply[A, B](implicit ev: A <~< B): F[B] <~< F[A] = A.map(_[A, B]).proved
    }
}
