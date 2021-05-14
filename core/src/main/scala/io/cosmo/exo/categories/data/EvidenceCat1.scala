package io.cosmo.exo.categories.data

import io.cosmo.exo.{-\/, /\, \/}
import io.cosmo.exo.categories.functors.LaxSemigroupal
import io.cosmo.exo.categories.{Cartesian, Endobifunctor, Subcat}

final case class EvidenceCat1[T1[_], T2[_], A, B](left: T1[A], right: T2[B])

object EvidenceCat1 {
  def id[T1[_], T2[_], A](implicit t1: T1[A], t2: T2[A]): EvidenceCat1[T1, T2, A, A] = EvidenceCat1(t1, t2)

  implicit def fromImplicits[T1[_], T2[_], A, B](implicit t1: T1[A], t2: T2[B]): EvidenceCat1[T1, T2, A, B] =
    EvidenceCat1(t1, t2)

  implicit def category[T1[_], T2[_]]: Subcat.Aux[EvidenceCat1[T1, T2, *, *], λ[a => T1[a] /\ T2[a]]] =
    new Subcat[EvidenceCat1[T1, T2, *, *]] {
      type TC[a] = T1[a] /\ T2[a]
      def id[A](implicit t: TC[A]) = EvidenceCat1.id(t._1, t._2)
      def andThen[A, B, C](ab: EvidenceCat1[T1, T2, A, B], bc: EvidenceCat1[T1, T2, B, C]) =
        EvidenceCat1(ab.left, bc.right)
    }

  implicit def bifunctorConj[T1[_], T2[_]](implicit
    L1: LaxSemigroupal[/\, * => *, /\, T1],
    L2: LaxSemigroupal[/\, * => *, /\, T2],
  ): Endobifunctor[EvidenceCat1[T1, T2, *, *], /\] = new Endobifunctor[EvidenceCat1[T1, T2, *, *], /\] {
    def bimap[A, X, B, Y](l: EvidenceCat1[T1, T2, A, X], r: EvidenceCat1[T1, T2, B, Y]) =
      EvidenceCat1(L1.product(/\(l.left, r.left)), L2.product(/\(l.right, r.right)))
  }

  implicit def bifunctorDisj[T1[_], T2[_]](implicit
    L1: LaxSemigroupal[\/, * => *, \/, T1],
    L2: LaxSemigroupal[\/, * => *, \/, T2],
  ): Endobifunctor[EvidenceCat1[T1, T2, *, *], \/] = new Endobifunctor[EvidenceCat1[T1, T2, *, *], \/] {
    def bimap[A, X, B, Y](l: EvidenceCat1[T1, T2, A, X], r: EvidenceCat1[T1, T2, B, Y]): EvidenceCat1[T1, T2, A \/ B, X \/ Y] =
      EvidenceCat1(L1.product[A, B](-\/(l.left)), L2.product[X, Y](-\/(l.right)))
  }

  implicit def cartesian[T1[_], T2[_], I](implicit
    L1: LaxSemigroupal[(*, *), * => *, (*, *), T1], t1: T1[I],
    L2: LaxSemigroupal[(*, *), * => *, (*, *), T2], t2: T2[I],
  ): Cartesian.Aux[EvidenceCat1[T1, T2, *, *], (*, *), λ[a => (T1[a], T2[a])], I] =
    new Cartesian[EvidenceCat1[T1, T2, *, *], (*, *)] {
      type TC[a] = (T1[a], T2[a])
      type Id = I
      def C = ???
      def bifunctor = ???
      def fst[A, B](implicit a: TC[A], b: TC[B]) = EvidenceCat1(L1.product((a._1, b._1)), a._2)
      def snd[A, B](implicit a: TC[A], b: TC[B]) = EvidenceCat1(L1.product((a._1, b._1)), b._2)
      def diag[A](implicit a: TC[A]) = EvidenceCat1(a._1, L2.product((a._2, a._2)))
      def &&&[X, Y, Z](f: EvidenceCat1[T1, T2, X, Y], g: EvidenceCat1[T1, T2, X, Z]) =
        EvidenceCat1(f.left, L2.product((f.right, g.right)))
      def idl  [A](implicit a: TC[A]) = EvidenceCat1(L1.product((t1, a._1)), a._2)
      def coidl[A](implicit a: TC[A]) = EvidenceCat1(a._1, L2.product((t2, a._2)))
      def idr  [A](implicit a: TC[A]) = EvidenceCat1(L1.product((a._1, t1)), a._2)
      def coidr[A](implicit a: TC[A]) = EvidenceCat1(a._1, L2.product((a._2, t2)))
      def braid[A, B](implicit a: TC[A], b: TC[B]) = EvidenceCat1(L1.product((a._1, b._1)), L2.product((b._2, a._2)))
      def associate  [X, Y, Z](implicit x: TC[X], y: TC[Y], z: TC[Z]) =
        EvidenceCat1(L1.product((L1.product((x._1, y._1)), z._1)), L2.product((x._2, L2.product((y._2, z._2)))))
      def diassociate[X, Y, Z](implicit x: TC[X], y: TC[Y], z: TC[Z]) = {
        EvidenceCat1(L1.product((x._1, L1.product((y._1, z._1)))), L2.product((L2.product((x._2, y._2)), z._2)))
      }
    }

  implicit def cartesian1[T1[_], T2[_], I](implicit
    L1: LaxSemigroupal[/\, * => *, /\, T1], t1: T1[I],
    L2: LaxSemigroupal[/\, * => *, /\, T2], t2: T2[I],
  ): Cartesian.Aux[EvidenceCat1[T1, T2, *, *], /\, λ[a => T1[a] /\ T2[a]], I] =
    new Cartesian[EvidenceCat1[T1, T2, *, *], /\] {
      type TC[a] = T1[a] /\ T2[a]
      type Id = I
      def C = category
      def bifunctor = bifunctorConj
      def fst[A, B](implicit a: TC[A], b: TC[B]) = EvidenceCat1(L1.product(/\(a._1, b._1)), a._2)
      def snd[A, B](implicit a: TC[A], b: TC[B]) = EvidenceCat1(L1.product(/\(a._1, b._1)), b._2)
      def diag[A](implicit a: TC[A]) = EvidenceCat1(a._1, L2.product(/\(a._2, a._2)))
      def &&&[X, Y, Z](f: EvidenceCat1[T1, T2, X, Y], g: EvidenceCat1[T1, T2, X, Z]) =
        EvidenceCat1(f.left, L2.product(/\(f.right, g.right)))
      def idl  [A](implicit a: TC[A]) = EvidenceCat1(L1.product(/\(t1, a._1)), a._2)
      def coidl[A](implicit a: TC[A]) = EvidenceCat1(a._1, L2.product(/\(t2, a._2)))
      def idr  [A](implicit a: TC[A]) = EvidenceCat1(L1.product(/\(a._1, t1)), a._2)
      def coidr[A](implicit a: TC[A]) = EvidenceCat1(a._1, L2.product(/\(a._2, t2)))
      def braid[A, B](implicit a: TC[A], b: TC[B]) = EvidenceCat1(L1.product(/\(a._1, b._1)), L2.product(/\(b._2, a._2)))
      def associate  [X, Y, Z](implicit x: TC[X], y: TC[Y], z: TC[Z]) =
        EvidenceCat1(L1.product(/\(L1.product(/\(x._1, y._1)), z._1)), L2.product(/\(x._2, L2.product(/\(y._2, z._2)))))
      def diassociate[X, Y, Z](implicit x: TC[X], y: TC[Y], z: TC[Z]) =
        EvidenceCat1(L1.product(/\(x._1, L1.product(/\(y._1, z._1)))), L2.product(/\(L2.product(/\(x._2, y._2)), z._2)))
    }

}