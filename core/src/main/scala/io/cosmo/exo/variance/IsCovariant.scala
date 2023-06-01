package io.cosmo.exo.variance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.inhabitance.*

trait IsCovariant[F[_]] { F =>

  def apply[A, B](using ab: A <~< B): F[A] <~< F[B]

  def substCo[G[+_], A, B](g: G[F[A]])(using ev: A <~< B): G[F[B]] =
    F(using ev).substCv[G](g)

  def substCt[G[-_], A, B](g: G[F[B]])(using ev: A <~< B): G[F[A]] =
    F(using ev).substCt[G](g)

  def coerce[A, B](value: F[A])(using ev: A <~< B): F[B] =
    F(using ev).coerce(value)

  def widen[A, B](fa: F[A])(using ev: A <~< B): F[B] =
    F(using ev).apply(fa)

  def composeCo[G[_]](G: IsCovariant[G]): IsCovariant[[x] =>> F[G[x]]] =
    IsCovariant.witness[[x] =>> F[G[x]]](using F(using G(using As.bottomTop)))

  def composeCt[G[_]](G: IsContravariant[G]): IsContravariant[[x] =>> F[G[x]]] =
    IsContravariant.witness[[x] =>> F[G[x]]](using F(using G(using As.bottomTop)))

  def composePh[G[_]](G: IsConstant[G]): IsConstant[[x] =>> F[G[x]]] =
    G.andThenCo[F](using F)
}
object IsCovariant {
  def apply[F[_]](using ev: IsCovariant[F]): IsCovariant[F] = ev

  def isoCanonic[F[_]]: Exo[<~<, <~<, F] <=> IsCovariant[F] =
    Iso.unsafe(
      exo => new IsCovariant[F] { def apply[A, B](using ev: A <~< B) = exo.map(ev) },
      isc => Exo.unsafe([A, B] => (fn: A <~< B) => isc.apply(using fn))
    )

  def witness[F[_]](using fab: F[Void] <~< F[Any]): IsCovariant[F] =
    witness1[F, Void, Any](using StrictAs.bottomTop, fab)

  def witness1[F[_], A, B](using ab: A </< B, fab: F[A] <~< F[B]): IsCovariant[F] =
    new IsCovariant[F] {
      override def apply[X, Y](using xy: X <~< Y): F[X] <~< F[Y] =
        Is.lem[X, Y].map {
          _.fold(neqv => Parametric[F].liftCv[A, B, X, Y](ab, fab, StrictAs.witness(neqv, xy)), eqv => eqv.lift[F].toAs)
        }.proved
    }

  given reify[F[+_]]: IsCovariant[F] =
    witness[F](using As.reify[F[Void], F[Any]])

  given id: IsCovariant[[a] =>> a] = reify[[a] =>> a]

  given proposition[F[_]]: Proposition[IsCovariant[F]] =
    Proposition.witness((A: ¬¬[IsCovariant[F]]) => new IsCovariant[F] {
      override def apply[A, B](using ev: A <~< B): F[A] <~< F[B] = A.map(_[A, B]).proved
    })

}
