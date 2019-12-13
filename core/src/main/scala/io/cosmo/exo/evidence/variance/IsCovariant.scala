package io.cosmo.exo.evidence.variance

import cats.Id
import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.evidence._

trait IsCovariant[F[_]] { F =>

  def apply[A, B](implicit ab: A <~< B): F[A] <~< F[B]

  def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    F(ev).substCv[G](g)

  def substCt[G[-_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    F(ev).substCt[G](g)

  def coerce[A, B](value: F[A])(implicit ev: A <~< B): F[B] =
    F(ev).coerce(value)

  def widen[A, B](fa: F[A])(implicit ev: A <~< B): F[B] =
    F(ev).apply(fa)

  def composeCo[G[_]](G: IsCovariant[G]): IsCovariant[λ[x => F[G[x]]]] =
    IsCovariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composeCt[G[_]](G: IsContravariant[G]): IsContravariant[λ[x => F[G[x]]]] =
    IsContravariant.witness[λ[x => F[G[x]]]](F(G(As.bottomTop)))

  def composePh[G[_]](G: IsConstant[G]): IsConstant[λ[x => F[G[x]]]] =
    G.andThenCo[F](F)
}
object IsCovariant {
  def apply[F[_]](implicit ev: IsCovariant[F]): IsCovariant[F] = ev

  def witness[F[_]](implicit fab: F[Void] <~< F[Any]): IsCovariant[F] =
    witness1[F, Void, Any](StrictAs.bottomTop, fab)

  def witness1[F[_], A, B](implicit ab: A </< B, fab: F[A] <~< F[B]): IsCovariant[F] =
    new IsCovariant[F] {
      override def apply[X, Y](implicit xy: X <~< Y): F[X] <~< F[Y] =
        Is.lem[X, Y].map {
          _.fold(neqv => Parametric[F].liftCv[A, B, X, Y](ab, fab, StrictAs.witness(neqv, xy)), eqv => eqv.lift[F].toAs)
        }.proved
    }

  implicit def reify[F[+_]]: IsCovariant[F] =
    witness[F](As.reify[F[Void], F[Any]])

  implicit def id: IsCovariant[Id] = { type f[+x] = x; reify[f] }

  implicit def proposition[F[_]]: Proposition[IsCovariant[F]] =
    (A: ¬¬[IsCovariant[F]]) => new IsCovariant[F] {
      override def apply[A, B](implicit ev: A <~< B): F[A] <~< F[B] = A.map(_[A, B]).proved
    }
}