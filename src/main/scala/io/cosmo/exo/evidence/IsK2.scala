package io.cosmo.exo.evidence

import io.cosmo.exo.*
import io.cosmo.exo.inhabitance.*

sealed abstract class IsK2[F[_,_], G[_,_]]:
  fg =>

  def subst[Alg[_[_,_]]](fa: Alg[F]): Alg[G]

  final def apply[X, Y](a: F[X, Y]): G[X, Y] = coerce[X, Y](a)

  final def coerce[X, Y](a: F[X, Y]): G[X, Y] = subst[[f[_,_]] =>> f[X,Y]](a)

  final def andThen[H[_,_]](bc: G =~~= H): F =~~= H = bc.subst[[x[_,_]] =>> F =~~= x[_,_]](fg)

  final def compose[E[_,_]](za: E =~~= F): E =~~= G = za.andThen(fg)

  final def flip: G =~~= F = fg.subst[[x[_,_]] =>> x =~~= F](IsK2.refl[F])

  final def lower[T[_[_,_]]]: T[F] === T[G] = IsK2.lower[T, F, G](fg)

  final def is[A, B]: F[A, B] === G[A, B] = subst[[f[_,_]] =>> F[A,B] === f[A,B]](Is.refl[F[A, B]])

  final def toIso: F <~~> G = ∀∀.mk[F <~~> G].from(is.toIso)

object IsK2:
  given proposition[A[_, _], B[_, _]]: Proposition[A =~~= B] =
    Proposition.witness(p => Axioms.isK2Consistency[A, B](p: ((A =~~= B) => Void) => Void))

  def apply[A[_, _], B[_, _]](using ab: A =~~= B): A =~~= B = ab

  given refl[A[_, _]]: IsK2[A, A] with
    def subst[Alg[_[_, _]]](fa: Alg[A]): Alg[A] = fa

  given isoExtensionality[F[_, _], G[_, _]]: (∀∀[[a, b] =>> F[a, b] === G[a, b]] <=> (F =~~= G)) =
    Iso.unsafe(
      fa => Axioms.tcExtensionality2[F, G].applyT([A, B] => () => fa[A, B]),
      fg => ∀∀.of[[a, b] =>> F[a, b] === G[a, b]].from(fg.is)
    )

  /** Given `F =~= G` we can prove that `A[F] === A[G]`. */
  def lower[A[_[_,_]], F[_,_], G[_,_]](ab: F =~~= G): A[F] === A[G] = ab.subst[[a[_,_]] =>> A[F] === A[a]](Is.refl[A[F]])
  def lower2[A[_[_,_], _[_,_]]] = new Lower2Op[A] {}
  class Lower2Op[A[_[_,_], _[_,_]]]:
    def on[F[_,_], F1[_,_], G[_,_], G1[_,_]](
                                              ff: F =~~= F1, fg: G =~~= G1,
                                            ): A[F, G] === A[F1, G1] = ff.lower[[f[_,_]] =>> A[f, G]] andThen fg.lower[[f[_,_]] =>> A[F1, f]]

  def lower3[A[_[_,_], _[_,_], _[_,_]]] = new Lower3Op[A] {}
  class Lower3Op[A[_[_,_], _[_,_], _[_,_]]]:
    def on[F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_]](
                                                               ff: F =~~= F1, fg: G =~~= G1, fh: H =~~= H1
                                                             ): A[F, G, H] === A[F1, G1, H1] =
      ff.lower[[f[_,_]] =>> A[f, G, H]] andThen fg.lower[[f[_,_]] =>> A[F1, f, H]] andThen
        fh.lower[[f[_,_]] =>> A[F1, G1, f]]

  def lower4[A[_[_,_], _[_,_], _[_,_], _[_,_]]] = new Lower4Op[A] {}
  class Lower4Op[A[_[_,_], _[_,_], _[_,_], _[_,_]]]:
    def on[F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_], I[_,_], I1[_,_]](
                                                                                ff: F =~~= F1, fg: G =~~= G1, fh: H =~~= H1, fi: I =~~= I1
                                                                              ): A[F, G, H, I] === A[F1, G1, H1, I1] =
      ff.lower[[f[_,_]] =>> A[f, G, H, I]] andThen fg.lower[[f[_,_]] =>> A[F1, f, H, I]] andThen
        fh.lower[[f[_,_]] =>> A[F1, G1, f, I]] andThen fi.lower[[f[_,_]] =>> A[F1, G1, H1, f]]

end IsK2
