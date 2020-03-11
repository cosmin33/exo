package io.cosmo.exo.categories.data

import io.cosmo.exo.categories.Groupoid
import io.cosmo.exo.~>

final case class EvidenceCat[T[_], A, B](left: T[A], right: T[B]) {
  def andThen[C](that: EvidenceCat[T, B, C]): EvidenceCat[T, A, C] =
    new EvidenceCat[T, A, C](this.left, that.right)
  def compose[C](that: EvidenceCat[T, C, A]): EvidenceCat[T, C, B] =
    new EvidenceCat[T, C, B](that.left, this.right)

  def flip: EvidenceCat[T, B, A] =
    new EvidenceCat[T, B, A](this.right, this.left)

  def lift[F[_]](f: T ~> λ[X => T[F[X]]]): EvidenceCat[T, F[A], F[B]] =
    new EvidenceCat[T, F[A], F[B]](f.apply(left), f.apply(right))
  def liftT[F[_]](f: T ~> λ[X => T[F[X]]]): EvidenceCat[λ[X => T[F[X]]], A, B] =
    new EvidenceCat[λ[X => T[F[X]]], A, B](f.apply(left), f.apply(right))
}
object EvidenceCat {
  def id[T[_], A](implicit A: T[A]): EvidenceCat[T, A, A] =
    new EvidenceCat[T, A, A](A, A)

  implicit def category[T[_]]: Groupoid.Aux[EvidenceCat[T, *, *], T] =
    new Groupoid[EvidenceCat[T, *, *]] {
      override type TC[a] = T[a]
      override def id[A](implicit A: T[A]): EvidenceCat[T, A, A] =
        EvidenceCat.id[T, A](A)
      override def andThen[A, B, C](ab: EvidenceCat[T, A, B], bc: EvidenceCat[T, B, C]): EvidenceCat[T, A, C] =
        ab andThen bc
      override def flip[A, B](f: EvidenceCat[T, A, B]): EvidenceCat[T, B, A] =
        f.flip
    }
}