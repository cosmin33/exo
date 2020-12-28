package io.cosmo.exo.categories.data

import io.cosmo.exo.categories.{Cartesian, Endobifunctor, Groupoid, Monoidal, Subcat}
import io.cosmo.exo.{<=>, Iso, ~>}

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

  implicit def fromImplicits[T[_], A, B](implicit ta: T[A], tb: T[B]): EvidenceCat[T, A, B] = EvidenceCat(ta, tb)

  implicit def iso[T[_], A, B]: EvidenceCat[T, A, B] <=> (T[A], T[B]) =
    Iso.unsafe(ev => (ev.left, ev.right), p => fromImplicits(p._1, p._2))

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

  def more[T[_], I] =
    new Monoidal[EvidenceCat[T,*,*], (*, *)] {
      type TC[x] = T[x]
      type Id = I
      def C: Subcat.Aux[EvidenceCat[T, *, *], T] = category[T]
      def idl[A]: EvidenceCat[T, (I, A), A] = {

        ???
      }
      def coidl[A]: EvidenceCat[T, A, (I, A)] = ???
      def idr[A]: EvidenceCat[T, (A, I), A] = ???
      def coidr[A]: EvidenceCat[T, A, (A, I)] = ???
      def bifunctor: Endobifunctor[EvidenceCat[T, *, *], Tuple2] = ???
      def associate[X, Y, Z]: EvidenceCat[T, ((X, Y), Z), (X, (Y, Z))] = ???
      def diassociate[X, Y, Z]: EvidenceCat[T, (X, (Y, Z)), ((X, Y), Z)] = ???
    }
//  def more[T[_], I]: Cartesian[EvidenceCat[T, *, *], Tuple2] {type TC[x] = T[x]; type Id = I} =
//    new Cartesian[EvidenceCat[T,*,*], (*, *)] {
//      type TC[x] = T[x]
//      type Id = I
//      def fst[A, B]: EvidenceCat[T, (A, B), A] = ???
//      def snd[A, B]: EvidenceCat[T, (A, B), B] = ???
//      def diag[A]: EvidenceCat[T, A, (A, A)] = ???
//      def &&&[X, Y, Z](f: EvidenceCat[T, X, Y], g: EvidenceCat[T, X, Z]): EvidenceCat[T, X, (Y, Z)] = ???
//      def braid[A, B]: EvidenceCat[T, (A, B), (B, A)] = ???
//      def idl[A]: EvidenceCat[T, (I, A), A] = ???
//      def coidl[A]: EvidenceCat[T, A, (I, A)] = ???
//      def idr[A]: EvidenceCat[T, (A, I), A] = ???
//      def coidr[A]: EvidenceCat[T, A, (A, I)] = ???
//      def C: Aux[EvidenceCat[T, *, *], T] = ???
//      def bifunctor: Endobifunctor[EvidenceCat[T, *, *], Tuple2] = ???
//      def associate[X, Y, Z]: EvidenceCat[T, ((X, Y), Z), (X, (Y, Z))] = ???
//      def diassociate[X, Y, Z]: EvidenceCat[T, (X, (Y, Z)), ((X, Y), Z)] = ???
//    }

}