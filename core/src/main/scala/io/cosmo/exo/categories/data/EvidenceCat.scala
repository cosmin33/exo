package io.cosmo.exo.categories.data

import io.cosmo.exo.categories.functors.{Exobifunctor, LaxSemigroupal}
import io.cosmo.exo.categories.{Cartesian, Dual, Endobifunctor, Groupoid, Opp, Subcat}
import io.cosmo.exo.{-\/, /\, <=>, Iso, \/, ~>}

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
    L: LaxSemigroupal.Endo[* => *, /\, T]
  ): Endobifunctor[EvidenceCat[T, *, *], /\] = new Endobifunctor[EvidenceCat[T, *, *], /\] {
    def bimap[A, X, B, Y](l: EvidenceCat[T, A, X], r: EvidenceCat[T, B, Y]): EvidenceCat[T, A /\ B, X /\ Y] =
      fromImplicits[T, A /\ B, X /\ Y](L.product(/\(l.left, r.left)), L.product(/\(l.right, r.right)))
  }

  implicit def bifunctorDisj[T[_]](implicit
    L: LaxSemigroupal.Endo[* => *, \/, T]
  ): Endobifunctor[EvidenceCat[T, *, *], \/] = new Endobifunctor[EvidenceCat[T, *, *], \/] {
    def bimap[A, X, B, Y](l: EvidenceCat[T, A, X], r: EvidenceCat[T, B, Y]): EvidenceCat[T, A \/ B, X \/ Y] =
      fromImplicits[T, A \/ B, X \/ Y](L.product[A, B](-\/(l.left)), L.product[X, Y](-\/(l.right)))
  }

  implicit def cartesian[T[_], I](implicit
    L: LaxSemigroupal.Endo[* => *, /\, T], ti: T[I]
  ): Cartesian.Aux[EvidenceCat[T, *, *], /\, T, I] =
    new Cartesian[EvidenceCat[T,*,*], /\] {
      type TC[x] = T[x]
      type Id = I
      def bifunctor = EvidenceCat.bifunctorConj
      def C: Subcat.Aux[EvidenceCat[T, *, *], T] = category[T]
      def associate  [X: TC, Y: TC, Z: TC] = implicitly
      def diassociate[X: TC, Y: TC, Z: TC] = implicitly
      def idl  [A: TC]                     = implicitly
      def coidl[A: TC]                     = implicitly
      def idr  [A: TC]                     = implicitly
      def coidr[A: TC]                     = implicitly
      def fst[A: TC, B: TC]                = implicitly
      def snd[A: TC, B: TC]                = implicitly
      def diag[A: TC]                      = implicitly
      def braid[A: TC, B: TC]              = implicitly
      def &&&[X, Y, Z](f: EvidenceCat[T, X, Y], g: EvidenceCat[T, X, Z]) = EvidenceCat(f.left, L.product(/\(f.right, g.right)))
    }

  implicit def cocartesian[T[_], I](implicit
    L: LaxSemigroupal.Endo[* => *, \/, T], ti: T[I]
  ): Cartesian.Aux[Dual[EvidenceCat[T,*,*], *, *], \/, T, I] =
    Dual.leibniz[EvidenceCat[T,*,*]].subst[Cartesian.Aux[*[_,_], \/, T, I]](cocartesianOpp[T, I])

  implicit def cocartesianOpp[T[_], I](implicit
    L: LaxSemigroupal.Endo[* => *, \/, T], ti: T[I]
  ): Cartesian.Aux[Opp[EvidenceCat[T, *, *]]#l, \/, T, I] =
    new Cartesian[Opp[EvidenceCat[T,*,*]]#l, \/] {
        type Id = I
        type TC[a] = T[a]
        def C = category[T].opp
        def bifunctor = Exobifunctor.opp(EvidenceCat.bifunctorDisj)
        def associate  [X: TC, Y: TC, Z: TC] = implicitly
        def diassociate[X: TC, Y: TC, Z: TC] = implicitly
        def fst[A: TC, B: TC]                = implicitly
        def snd[A: TC, B: TC]                = implicitly
        def diag[A: TC]                      = implicitly
        def braid[A: TC, B: TC]              = implicitly
        def idl  [A: TC]                     = implicitly
        def coidl[A: TC]                     = implicitly
        def idr  [A: TC]                     = implicitly
        def coidr[A: TC]                     = implicitly
        def &&&[X, Y, Z](f: EvidenceCat[T, Y, X], g: EvidenceCat[T, Z, X]) = EvidenceCat(L.product(-\/(f.left)), f.right)
      }

}