package io.cosmo.exo.categories.data

import io.cosmo.exo.categories.functors.{LaxSemigroupal, OplaxSemigroupal}
import io.cosmo.exo.categories.{Cartesian, Dual, Endobifunctor, Groupoid, Monoidal, Opp, Subcat}
import io.cosmo.exo.{-\/, /\, <=>, Disjunction, DisjunctionModule, Iso, \/, \/-, ~>}

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

  implicit def bifunctorConj[T[_]](implicit
    L: LaxSemigroupal.Endo[* => *, /\, T]
  ): Endobifunctor[EvidenceCat[T, *, *], /\] = new Endobifunctor[EvidenceCat[T, *, *], /\] {
    def bimap[A, X, B, Y](l: EvidenceCat[T, A, X], r: EvidenceCat[T, B, Y]): EvidenceCat[T, A /\ B, X /\ Y] =
      fromImplicits[T, A /\ B, X /\ Y](L.product(/\(l.left, r.left)), L.product(/\(l.right, r.right)))
  }

  implicit def bifunctorDisj[T[_]](implicit
    L: LaxSemigroupal[Dual[* => *,*,*], \/, * => *, \/, T]
  ): Endobifunctor[EvidenceCat[T, *, *], \/] = new Endobifunctor[EvidenceCat[T, *, *], \/] {
    def bimap[A, X, B, Y](l: EvidenceCat[T, A, X], r: EvidenceCat[T, B, Y]): EvidenceCat[T, A \/ B, X \/ Y] =
      fromImplicits[T, A \/ B, X \/ Y](L.product[A, B](-\/(l.left)), L.product[X, Y](-\/(l.right)))
  }

  implicit def bifunctorEither[T[_]](implicit
    L: LaxSemigroupal[Opp[* => *]#l, \/, * => *, \/, T]
  ): Endobifunctor[Opp[EvidenceCat[T, *, *]]#l, \/] = new Endobifunctor[Opp[EvidenceCat[T, *, *]]#l, \/] {
    def bimap[A, X, B, Y](l: EvidenceCat[T, X, A], r: EvidenceCat[T, Y, B]): EvidenceCat[T, X \/ Y, A \/ B] =
      fromImplicits[T, X \/ Y, A \/ B](L.product[X, Y](-\/(l.left)), L.product[A, B](-\/(l.right)))
  }

  def cartesian[T[_], I](implicit
    ti: T[I],
    L: LaxSemigroupal[* => *, /\, * => *, /\, T]
  ) =
    new Cartesian[EvidenceCat[T,*,*], /\] {
      type TC[x] = T[x]
      type Id = I
      def bifunctor = EvidenceCat.bifunctorConj
      def C: Subcat.Aux[EvidenceCat[T, *, *], T] = category[T]
      def idl  [A: TC]: EvidenceCat[T, I /\ A, A] = fromImplicits
      def coidl[A: TC]: EvidenceCat[T, A, I /\ A] = fromImplicits
      def idr  [A: TC]: EvidenceCat[T, A /\ I, A] = fromImplicits
      def coidr[A: TC]: EvidenceCat[T, A, A /\ I] = fromImplicits
      def associate  [X: TC, Y: TC, Z: TC]: EvidenceCat[T, X /\ Y /\ Z, X /\ (Y /\ Z)] = fromImplicits
      def diassociate[X: TC, Y: TC, Z: TC]: EvidenceCat[T, X /\ (Y /\ Z), X /\ Y /\ Z] = fromImplicits
      def fst[A: TC, B: TC]: EvidenceCat[T, A /\ B, A] = fromImplicits
      def snd[A: TC, B: TC]: EvidenceCat[T, A /\ B, B] = fromImplicits
      def diag[A: TC]: EvidenceCat[T, A, A /\ A] = fromImplicits
      def &&&[X, Y, Z](f: EvidenceCat[T, X, Y], g: EvidenceCat[T, X, Z]): EvidenceCat[T, X, Y /\ Z] =
        EvidenceCat(f.left, L.product(/\(f.right, g.right)))
      def braid[A: TC, B: TC]: EvidenceCat[T, A /\ B, B /\ A] = fromImplicits
    }

  def cocartesian[T[_], I](implicit
    ti: T[I],
    L: LaxSemigroupal[Opp[* => *]#l, \/, * => *, \/, T]
  ) = new Cartesian[Opp[EvidenceCat[T,*,*]]#l, \/] {
        type Id = I
        type TC[a] = T[a]
        def bifunctor = EvidenceCat.bifunctorEither
        def fst[A: TC, B: TC]: EvidenceCat[T, A, A \/ B] = {
          //fromImplicits[TC, A, A \/ B]
          //val tab = DisjunctionModule.primary[A, B]
          ???
        }
        def snd[A: TC, B: TC] = ???
        def diag[A: TC] = ???
        def &&&[X, Y, Z](f: EvidenceCat[T, Y, X], g: EvidenceCat[T, Z, X]) = ???
        def braid[A: TC, B: TC]  = ???
        def idl[A: TC]  = ???
        def coidl[A: TC]  = ???
        def idr[A: TC]  = ???
        def coidr[A: TC]  = ???
        def C = ???
        def associate  [X: TC, Y: TC, Z: TC]  = ???
        def diassociate[X: TC, Y: TC, Z: TC]  = ???
      }

}