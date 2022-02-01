package io.cosmo.exo.categories.data

import io.cosmo.exo._
import io.cosmo.exo.categories.functors.LaxSemigroupal
import io.cosmo.exo.categories.{Endobifunctor, Groupoid}

final case class EvidenceCat[T[_], A, B](left: T[A], right: T[B]) {
  def andThen[C](that: EvidenceCat[T, B, C]): EvidenceCat[T, A, C] =
    new EvidenceCat[T, A, C](this.left, that.right)
  def compose[C](that: EvidenceCat[T, C, A]): EvidenceCat[T, C, B] =
    new EvidenceCat[T, C, B](that.left, this.right)

  def flip: EvidenceCat[T, B, A] =
    new EvidenceCat[T, B, A](this.right, this.left)

  def lift[F[_]](f: T ~> λ[a => T[F[a]]]): EvidenceCat[T, F[A], F[B]] =
    new EvidenceCat[T, F[A], F[B]](f.apply(left), f.apply(right))
  def liftT[F[_]](f: T ~> λ[a => T[F[a]]]): EvidenceCat[λ[X => T[F[X]]], A, B] =
    new EvidenceCat[λ[a => T[F[a]]], A, B](f.apply(left), f.apply(right))
}

object EvidenceCat {
  def id[T[_], A](implicit A: T[A]): EvidenceCat[T, A, A] = new EvidenceCat[T, A, A](A, A)

  implicit def fromImplicits[T[_], A, B](implicit ta: T[A], tb: T[B]): EvidenceCat[T, A, B] = EvidenceCat(ta, tb)

  implicit def iso[T[_], A, B]: EvidenceCat[T, A, B] <=> (T[A], T[B]) =
    Iso.unsafe(ev => (ev.left, ev.right), p => fromImplicits(p._1, p._2))

  implicit def category[T[_]]: Groupoid.Aux[EvidenceCat[T, *, *], T] =
    new Groupoid[EvidenceCat[T, *, *]] {
      type TC[a] = T[a]
      def id[A](implicit A: T[A]): EvidenceCat[T, A, A] = EvidenceCat.id[T, A](A)
      def andThen[A, B, C](ab: EvidenceCat[T, A, B], bc: EvidenceCat[T, B, C]): EvidenceCat[T, A, C] = ab andThen bc
      def flip[A, B](f: EvidenceCat[T, A, B]): EvidenceCat[T, B, A] = f.flip
    }

  implicit def bifunctorConj[T[_]](implicit
    L: LaxSemigroupal[/\, * => *, /\, T]
  ): Endobifunctor[EvidenceCat[T, *, *], /\] = new Endobifunctor[EvidenceCat[T, *, *], /\] {
    def bimap[A, X, B, Y](l: EvidenceCat[T, A, X], r: EvidenceCat[T, B, Y]): EvidenceCat[T, A /\ B, X /\ Y] =
      fromImplicits[T, A /\ B, X /\ Y](L.product(/\(l.left, r.left)), L.product(/\(l.right, r.right)))
  }

}