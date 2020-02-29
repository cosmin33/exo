package io.cosmo.exo.evidence

import io.cosmo.exo
import io.cosmo.exo._
import io.cosmo.exo.typeclasses.TypeF

sealed abstract class IsK[F[_], G[_]] private[IsK]() { ab =>
  import IsK._

  def subst[Alg[_[_]]](fa: Alg[F]): Alg[G]

  final def apply[X](a: F[X]): G[X] = coerce[X](a)

  final def coerce[X](a: F[X]): G[X] = subst[λ[f[_] => f[X]]](a)

  final def andThen[H[_]](bc: G =~= H): F =~= H = bc.subst[F =~= *[_]](ab)

  final def compose[E[_]](za: E =~= F): E =~= G = za.andThen(ab)

  final def flip: G =~= F = ab.subst[*[_] =~= F](refl)

  final def lower[T[_[_]]]: T[F] === T[G] = IsK.lower[T, F, G](ab)

  /** Given `F =~= G` and `I =~= J` we can prove that `T[F, I] === T[G, J]`. */
  final def lower2[T[_[_], _[_]]]: PartiallyAppliedLower2[T] = new PartiallyAppliedLower2[T]
  final class PartiallyAppliedLower2[T[_[_], _[_]]] {
    def apply[I[_], J[_]](ij: I =~= J): T[F, I] === T[G, J] =
      IsK.lower2[T, F, G, I, J](ab, ij)
  }

  /** Given `F =~= G` we can prove that `T[F, ?] =~= T[G, ?]`. */
  final def lift[T[_[_], _]]: T[F, *] =~= T[G, *] = IsK.lift(ab)

  /** Given `F =~= G` and `I =~= J` we can prove that `T[F, I, ?] =~= T[G, J, ?]`. */
  final def lift2[T[_[_], _[_], _]]: PartiallyAppliedLift2[T] = new PartiallyAppliedLift2[T]
  final class PartiallyAppliedLift2[T[_[_], _[_], _]] {
    def apply[I[_], J[_]](ij: I =~= J): T[F, I, *] =~= T[G, J, *] =
      IsK.lift2(ab, ij)
  }

  final def is[A]: F[A] === G[A] = subst[λ[f[_] => F[A] === f[A]]](Is.refl[F[A]])

  final def toIso: F <~> G = ∀.mk[F <~> G].from(is.toIso)

}

object IsK {
  private[this] final case class Refl[A[_]]() extends IsK[A, A] {
    def subst[F[_[_]]](fa: F[A]): F[A] = fa
  }

  lazy val forall = ForallK.of[λ[f[_] => f =~= f]].fromH(t => new Refl[t.T]())

  private type ForallFG[F[_], G[_]] = ForallHK[λ[a[_[_]] => a[F] <=> a[G]]]
  def isoCanonic[F[_], G[_]]: ForallFG[F, G] <=> (F =~= G) =
    Iso.unsafe(
      fa => new IsK[F, G] { def subst[Alg[_[_]]](f: Alg[F]): Alg[G] = fa[Alg].to(f) },
      ev => ForallHK.mk[ForallFG[F, G]].from(Iso.unsafe(ev.subst, ev.flip.subst))
    )
  def isoExtensionality[F[_], G[_]]: ∀[λ[a => F[a] === G[a]]] <=> (F =~= G) =
    Iso.unsafe(
      fa => Axioms.tcExtensionality[F, G].applyT(t => fa[t.T]),
      fg => ∀.of[λ[a => F[a] === G[a]]].from(fg.is)
    )

  def isoTypeFInjectivity[F[_], G[_]]: (TypeF[F] === TypeF[G]) <=> (F =~= G) =
    Iso.unsafe(TypeF.injectivity, _.lower[TypeF])

//  def isoInjectivity[F[_], G[_], X[_]]: (F =~= G) <=> (λ[a => X[F[a]]] =~= λ[a => X[G[a]]]) =
//    Iso.unsafe[* => *, F =~= G, λ[a => X[F[a]]] =~= λ[a => X[G[a]]]](
//
//    )

  implicit def proposition[A[_], B[_]]: Proposition[A =~= B] =
    (p: ¬¬[A =~= B]) => Axioms.isKConsistency[A, B](p.run)

  def apply[A[_], B[_]](implicit ab: A =~= B): A =~= B = ab

  implicit def refl[A[_]]: A =~= A = forall.apply[A]

  /** Given `F =~= G` we can prove that `A[F] === A[G]`. */
  def lower[A[_[_]], F[_], G[_]](ab: F =~= G): A[F] === A[G] = ab.subst[λ[a[_] => A[F] === A[a]]](Is.refl[A[F]])

  def const[A, B](ab: A === B): λ[x => A] =~= λ[x => B] = {
    type f[a] = λ[x => A] =~= λ[x => a]
    ab.subst[f](IsK.refl[λ[x => A]])
  }

  /** Given `A =~= B` and `I =~= J` we can prove that `F[A, I] === F[B, J]`. */
  def lower2[F[_[_], _[_]], A[_], B[_], I[_], J[_]]
  (ab: A =~= B, ij: I =~= J): F[A, I] === F[B, J] = {
    type f1[a[_]] = F[A, I] === F[a, I]
    type f2[i[_]] = F[A, I] === F[B, i]
    ij.subst[f2](ab.subst[f1](Is.refl))
  }

  /** Given `A =~= B`, `I =~= J`, and `M =~= N` we can prove that `F[A, I] === F[B, J]`. */
  def lower3[F[_[_], _[_], _[_]], A[_], B[_], I[_], J[_], M[_], N[_]]
  (ab: A =~= B, ij: I =~= J, mn: M =~= N): F[A, I, M] === F[B, J, N] = {
    type f1[a[_]] = F[A, I, M] === F[a, I, M]
    type f2[i[_]] = F[A, I, M] === F[B, i, M]
    type f3[j[_]] = F[A, I, M] === F[B, J, j]
    mn.subst[f3](ij.subst[f2](ab.subst[f1](Is.refl)))
  }

  /** Given `A =~= B` we can prove that `F[A, ?] =~= F[B, ?]`. */
  def lift[F[_[_], *], A[_], B[_]]
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