package io.cosmo.exo.variance

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.inhabitance.*

trait IsContravariant[F[_]] { self =>

  def apply[A, B](using ab: A <~< B): F[B] <~< F[A]

  def substCo[G[+_], A, B](g: G[F[B]])(using ev: A <~< B): G[F[A]] = self(using ev).substCv[G](g)

  def substCt[G[-_], A, B](g: G[F[A]])(using ev: A <~< B): G[F[B]] = self(using ev).substCt[G](g)

  def coerce[A, B](fb: F[B])(using ev: A <~< B): F[A] = self(using ev).coerce(fb)

  def widen[A, B](fb: F[B])(using ev: A <~< B): F[A] = coerce(fb)

  def composeCo[G[_]](G: IsCovariant[G]): IsContravariant[[x] =>> F[G[x]]] =
    IsContravariant.witness[[x] =>> F[G[x]]](using self(using G(using As.bottomTop)))

  def composeCt[G[_]](G: IsContravariant[G]): IsCovariant[[x] =>> F[G[x]]] =
    IsCovariant.witness[[x] =>> F[G[x]]](using self(using G(using As.bottomTop)))

  def composePh[G[_]](G: IsConstant[G]): IsConstant[[x] =>> F[G[x]]] = G.andThenCt[F](using self)
}

object IsContravariant:

  def apply[F[_]](using ev: IsContravariant[F]): IsContravariant[F] = ev

  def isoCanonic[F[_]]: Exo[Dual[<~<, *, *], <~<, F] <=> IsContravariant[F] =
    Iso.unsafe(
      exo => new IsContravariant[F] { def apply[A, B](using ev: A <~< B) = exo.map[B, A](Dual(ev)) },
      isc => Exo.unsafe([A, B] => (fn: Dual[<~<, A, B]) => isc.apply(using fn))
    )

  def witness[F[_]](using fba: F[Any] <~< F[Void]): IsContravariant[F] =
    witness1[F, Void, Any](using StrictAs.bottomTop, fba)

  def witness1[F[_], A, B](using ab: A </< B, fba: F[B] <~< F[A]): IsContravariant[F] =
    new IsContravariant[F]:
      override def apply[X, Y](using xy: X <~< Y): F[Y] <~< F[X] =
        Is.lem[X, Y].map {
          _.fold(
            neqv => Parametric[F].liftCt[A, B, X, Y](ab, fba, StrictAs.witness(using neqv, xy)),
            eqv => eqv.lift[F].flip.toAs
          )
        }.proved

  given reify[F[-_]]: IsContravariant[F] =
    witness[F](using As.reify[F[Any], F[Void]])

  given proposition[F[_]]: Proposition[IsContravariant[F]] =
    Proposition.witness((A: ¬¬[IsContravariant[F]]) => new IsContravariant[F] {
      override def apply[A, B](using ev: A <~< B): F[B] <~< F[A] = A.map(_[A, B]).proved
    })

end IsContravariant
