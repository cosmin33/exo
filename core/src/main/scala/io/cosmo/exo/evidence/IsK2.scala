package io.cosmo.exo.evidence

import io.cosmo.exo
import io.cosmo.exo._

sealed abstract class IsK2[F[_,_], G[_,_]] private[IsK2]() { ab =>
  import IsK2._

  def subst[Alg[_[_,_]]](fa: Alg[F]): Alg[G]

  final def apply[X, Y](a: F[X, Y]): G[X, Y] = coerce[X, Y](a)

  final def coerce[X, Y](a: F[X, Y]): G[X, Y] = subst[λ[f[_,_] => f[X,Y]]](a)

  final def andThen[H[_,_]](bc: G =~~= H): F =~~= H = bc.subst[F =~~= *[_,_]](ab)

  final def compose[E[_,_]](za: E =~~= F): E =~~= G = za.andThen(ab)

  final def flip: G =~~= F = ab.subst[*[_,_] =~~= F](refl)

  final def lower[T[_[_,_]]]: T[F] === T[G] = IsK2.lower[T, F, G](ab)

  final def is[A, B]: F[A, B] === G[A, B] = subst[λ[f[_,_] => F[A,B] === f[A,B]]](Is.refl[F[A, B]])

  final def toIso: F <~~> G = ∀∀.mk[F <~~> G].from(is.toIso)

}

object IsK2 {
  private[this] final class Refl[A[_,_]] extends IsK2[A, A] {
    def subst[F[_[_,_]]](fa: F[A]): F[A] = fa
  }

  implicit def proposition[A[_,_], B[_,_]]: Proposition[A =~~= B] =
    (p: ¬¬[A =~~= B]) => Axioms.isK2Consistency[A, B](p.run)

  def apply[A[_,_], B[_,_]](implicit ab: A =~~= B): A =~~= B = ab

  implicit def refl[A[_,_]]: A =~~= A = new Refl[A]

  /** Given `F =~= G` we can prove that `A[F] === A[G]`. */
  def lower[A[_[_,_]], F[_,_], G[_,_]](ab: F =~~= G): A[F] === A[G] = ab.subst[λ[a[_,_] => A[F] === A[a]]](Is.refl[A[F]])
  def lower2[A[_[_,_], _[_,_]]] = new Lower2Op[A] {}
  class Lower2Op[A[_[_,_], _[_,_]]] {
    def on[F[_,_], F1[_,_], G[_,_], G1[_,_]](
      ff: F =~~= F1, fg: G =~~= G1,
    ): A[F, G] === A[F1, G1] = ff.lower[A[*[_,_], G]] andThen fg.lower[A[F1, *[_,_]]]
  }
  def lower3[A[_[_,_], _[_,_], _[_,_]]] = new Lower3Op[A] {}
  class Lower3Op[A[_[_,_], _[_,_], _[_,_]]] {
    def on[F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_]](
    ff: F =~~= F1, fg: G =~~= G1, fh: H =~~= H1
  ): A[F, G, H] === A[F1, G1, H1] =
      ff.lower[A[*[_,_], G, H]] andThen fg.lower[A[F1, *[_,_], H]] andThen fh.lower[A[F1, G1, *[_,_]]]
  }
  def lower4[A[_[_,_], _[_,_], _[_,_], _[_,_]]] = new Lower4Op[A] {}
  class Lower4Op[A[_[_,_], _[_,_], _[_,_], _[_,_]]] {
    def on[F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_], I[_,_], I1[_,_]](
    ff: F =~~= F1, fg: G =~~= G1, fh: H =~~= H1, fi: I =~~= I1
  ): A[F, G, H, I] === A[F1, G1, H1, I1] =
    ff.lower[A[*[_,_], G, H, I]] andThen fg.lower[A[F1, *[_,_], H, I]] andThen
      fh.lower[A[F1, G1, *[_,_], I]] andThen fi.lower[A[F1, G1, H1, *[_,_]]]
  }
  def lower5[A[_[_,_], _[_,_], _[_,_], _[_,_], _[_,_]]] = new Lower5Op[A] {}
  class Lower5Op[A[_[_,_], _[_,_], _[_,_], _[_,_], _[_,_]]] {
    def on[F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_], I[_,_], I1[_,_], J[_,_], J1[_,_]](
    ff: F =~~= F1, fg: G =~~= G1, fh: H =~~= H1, fi: I =~~= I1, fj: J =~~= J1
  ): A[F, G, H, I, J] === A[F1, G1, H1, I1, J1] =
    ff.lower[A[*[_,_], G, H, I, J]] andThen fg.lower[A[F1, *[_,_], H, I, J]] andThen
      fh.lower[A[F1, G1, *[_,_], I, J]] andThen fi.lower[A[F1, G1, H1, *[_,_], J]] andThen
      fj.lower[A[F1, G1, H1, I1, *[_,_]]]
  }

  implicit def isoExtensionality[F[_,_], G[_,_]]: ∀∀[λ[(a,b) => F[a,b] === G[a,b]]] <=> (F =~~= G) =
    Iso.unsafe(
      fa => Axioms.tcExtensionality2[F, G].applyT(t => fa[t.A, t.B]),
      fg => ∀∀.of[λ[(a,b) => F[a,b] === G[a,b]]].from(fg.is)
    )
}