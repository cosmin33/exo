package io.cosmo.exo.evidence

import io.cosmo.exo.*

sealed abstract class IsHK[F[_[_]], G[_[_]]] { self =>
  def subst[A[_[_[_]]]](fa: A[F]): A[G]

  def coerce[X[_]](x: F[X]): G[X] = subst[[f[_[_]]] =>> f[X]](x)

  def andThen[H[_[_]]](that: IsHK[G, H]): IsHK[F, H] = that.subst[[x[_[_]]] =>> F =≈= x](self)

  def compose[E[_[_]]](that: IsHK[E, F]): IsHK[E, G] = that.andThen(self)

  def flip: IsHK[G, F] = subst[[x[_[_]]] =>> IsHK[x, F]](IsHK.refl[F])

  def lower[T[_[_[_]]]]: T[F] === T[G] = IsHK.lower[T, F, G](self)

  final def lift[T[_[_[_]], _]]: T[F, *] =~= T[G, *] = IsHK.lift[T, F, G](self)

  final def is[A[_]]: F[A] === G[A] = subst[[f[_[_]]] =>> F[A] === f[A]](Is.refl[F[A]])

//  final def toIso: F <≈> G = <≈>.unsafe([A[_]] => () => is[A].toIso)

}

object IsHK {
  def apply[F[_[_]], G[_[_]]](using ev: F =≈= G): F =≈= G = ev

  given refl[F[_[_]]]: IsHK[F, F] with
    def subst[A[_[_[_]]]](fa: A[F]): A[F] = fa

  def isoCanonic[F[_[_]], G[_[_]]]: ([A[_[_[_]]]] => A[F] => A[G]) <=> (F =≈= G) =
    Iso.unsafe[Function, [A[_[_[_]]]] => A[F] => A[G], F =≈= G](
      fa => new IsHK[F, G] { def subst[A[_[_[_]]]](a: A[F]): A[G] = fa[A](a) },
      ev => [A[_[_[_]]]] => (a: A[F]) => ev.subst[A](a)
    )

  def lower[T[_[_[_]]], F[_[_]], G[_[_]]](eq: F =≈= G): T[F] === T[G] = eq.subst[[x[_[_]]] =>> T[F] === T[x]](Is.refl)

  def lower2[F[_[_[_]], _[_[_]]], A[_[_]], B[_[_]], I[_[_]], J[_[_]]]
  (ab: A =≈= B, ij: I =≈= J): F[A, I] === F[B, J] = {
    type f1[a[_[_]]] = F[A, I] === F[a, I]
    type f2[i[_[_]]] = F[A, I] === F[B, i]
    ij.subst[f2](ab.subst[f1](Is.refl))
  }

  def lift[T[_[_[_]], _], F[_[_]], G[_[_]]](eq: F =≈= G): T[F, *] =~= T[G, *] = {
    type f[a[_[_]]] = T[F, *] =~= T[a, *]
    eq.subst[f](IsK.refl[T[F, *]])
  }

}

