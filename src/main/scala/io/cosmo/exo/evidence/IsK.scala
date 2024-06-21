package io.cosmo.exo.evidence

import io.cosmo.exo.*

sealed abstract class IsK[F[_], G[_]] { self =>
  def subst[A[_[_]]](fa: A[F]): A[G]

  def coerce[X](x: F[X]): G[X] = subst[[f[_]] =>> f[X]](x)

  def andThen[H[_]](that: IsK[G, H]): IsK[F, H] = that.subst[[x[_]] =>> F =~= x](self)

  def compose[E[_]](that: IsK[E, F]): IsK[E, G] = that.andThen(self)

  def flip: IsK[G, F] = subst[[x[_]] =>> IsK[x, F]](IsK.refl[F])

  /** Given `F =~= G` we can prove that for any T, T[F] === T[G] */
  def lower[T[_[_]]]: T[F] === T[G] = IsK.lower[T, F, G](self)

  /** Given `F =~= G` we can prove that for any T, `T[F, *] =~= T[G, *]`. */
  final def lift[T[_[_], _]]: T[F, *] =~= T[G, *] = IsK.lift[T, F, G](self)

  final def is[A]: F[A] === G[A] = subst[[f[_]] =>> F[A] === f[A]](Is.refl[F[A]])

  final def toIso: F <~> G = <~>.unsafe([A] => () => is[A].toIso)

}

object IsK {
  def apply[F[_], G[_]](using ev: F =~= G): F =~= G = ev

  given refl[F[_]]: IsK[F, F] with
    def subst[A[_[_]]](fa: A[F]): A[F] = fa

  def isoCanonic[F[_], G[_]]: ([A[_[_]]] => A[F] => A[G]) <=> (F =~= G) =
    Iso.unsafe[Function, [A[_[_]]] => A[F] => A[G], F =~= G](
      fa => new IsK[F, G] { def subst[A[_[_]]](a: A[F]): A[G] = fa[A](a) },
      ev => [A[_[_]]] => (a: A[F]) => ev.subst[A](a)
    )
  
  /** Given `F =~= G` we can prove that `A[F] === A[G]`. */
  def lower[A[_[_]], F[_], G[_]](eq: F =~= G): A[F] === A[G] = eq.subst[[x[_]] =>> A[F] === A[x]](Is.refl)

  def lower2[F[_[_], _[_]], A[_], B[_], I[_], J[_]]
  (ab: A =~= B, ij: I =~= J): F[A, I] === F[B, J] = {
    type f1[a[_]] = F[A, I] === F[a, I]
    type f2[i[_]] = F[A, I] === F[B, i]
    ij.subst[f2](ab.subst[f1](Is.refl))
  }

  def lower3[F[_[_], _[_], _[_]], A[_], B[_], I[_], J[_], M[_], N[_]]
  (ab: A =~= B, ij: I =~= J, mn: M =~= N): F[A, I, M] === F[B, J, N] = {
    type f1[a[_]] = F[A, I, M] === F[a, I, M]
    type f2[i[_]] = F[A, I, M] === F[B, i, M]
    type f3[j[_]] = F[A, I, M] === F[B, J, j]
    mn.subst[f3](ij.subst[f2](ab.subst[f1](Is.refl)))
  }

  def lower4[F[_[_], _[_], _[_], _[_]], A[_], X[_], B[_], Y[_], C[_], Z[_], D[_], T[_]]
  (ax: A =~= X, by: B =~= Y, cz: C =~= Z, dt: D =~= T): F[A, B, C, D] === F[X, Y, Z, T] = {
    type f1[a[_]] = F[A, B, C, D] === F[a, B, C, D]
    type f2[a[_]] = F[A, B, C, D] === F[X, a, C, D]
    type f3[a[_]] = F[A, B, C, D] === F[X, Y, a, D]
    type f4[a[_]] = F[A, B, C, D] === F[X, Y, Z, a]
    dt.subst[f4](cz.subst[f3](by.subst[f2](ax.subst[f1](Is.refl))))
  }

  /** Given `A =~= B` we can prove that `F[A, ?] =~= F[B, ?]`. */
  def lift[F[_[_], _], A[_], B[_]]
  (ab: A =~= B): F[A, *] =~= F[B, *] = {
    type f[a[_]] = F[A, *] =~= F[a, *]
    ab.subst[f](refl[F[A, *]])
  }

  /** Given `A =~= B` and `I =~= J` we can prove that `F[A, I, *] =~= F[B, J, *]`. */
  def lift2[F[_[_], _[_], _], A[_], B[_], I[_], J[_]]
  (ab: A =~= B, ij: I =~= J): F[A, I, *] =~= F[B, J, *] = {
    type f1[a[_]] = F[A, I, *] =~= F[a, I, *]
    type f2[i[_]] = F[A, I, *] =~= F[B, i, *]
    ij.subst[f2](ab.subst[f1](refl[F[A, I, *]]))
  }

  /** Given `A =~= B`, `I =~= J`, and `M =~= N` we can prove that `F[A, I, ?] =~= F[B, J, ?]`. */
  def lift3[F[_[_], _[_], _[_], _], A[_], B[_], I[_], J[_], M[_], N[_]]
  (ab: A =~= B, ij: I =~= J, mn: M =~= N): F[A, I, M, *] =~= F[B, J, N, *] = {
    type f1[a[_]] = F[A, I, M, *] =~= F[a, I, M, *]
    type f2[i[_]] = F[A, I, M, *] =~= F[B, i, M, *]
    type f3[j[_]] = F[A, I, M, *] =~= F[B, J, j, *]
    mn.subst[f3](ij.subst[f2](ab.subst[f1](refl[F[A, I, M, *]])))
  }

}

