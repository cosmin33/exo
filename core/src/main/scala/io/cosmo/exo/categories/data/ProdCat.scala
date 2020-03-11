package io.cosmo.exo.categories.data

import cats.data.Tuple2K
import io.cosmo.exo.categories
import io.cosmo.exo.categories.{Cartesian, Dual, Endobifunctor, Monoidal, Semicategory, Subcat}

final case class ProdCat[==>[_,_], -->[_,_], A, B](first: A ==> B, second: A --> B) { ab =>
//  def andThen[C](bc: ProdCat[==>, -->, B, C])(implicit C: Semicategory[==>], D: Semicategory[-->]): ProdCat[==>, -->, A, C] =
//    ProdCat(C.andThen(ab.first, bc.first), D.andThen(ab.second, bc.second))
}

object ProdCat {
//  type BicatEndo[->[_,_], A, B] = ProdCat[->, ->, A, B]
//  // TODO: trebuie sa inversez Dicat'ul: .. = ProdCat[Dual[->,*,*], ->, A, B]
//  // pentru ca la profunctori tre'sa fie contravariantul primul functor si covariantul al doilea
//  type DiCat[->[_,_], A, B] = ProdCat[->, Dual[->,*,*], A, B]
//  object DiCat {
//    def apply[->[_,_], A, B](to: A -> B, from: B -> A): DiCat[->, A, B] = new DiCat(to, Dual(from))
//  }
//
//  def id[==>[_,_], =>#[_], -->[_,_], ->#[_], A](implicit
//    C: Subcat.Aux[==>, =>#],
//    AC: =>#[A],
//    D: Subcat.Aux[-->, ->#],
//    AD: ->#[A],
//  ): ProdCat[==>, -->, A, A] = ProdCat(C.id[A](AC), D.id[A](AD))
//
//  def categoryTupledTc[==>[_,_], =>#[_], -->[_,_], ->#[_]](implicit
//    C: Subcat.Aux[==>, =>#], D: Subcat.Aux[-->, ->#]
//  ): Subcat.Aux[ProdCat[==>, -->, *, *], Tuple2K[=>#, ->#, *]] =
//    new Subcat[ProdCat[==>, -->, *, *]] {
//      type TC[a] = Tuple2K[=>#, ->#, a]
//      def id[A](implicit A: Tuple2K[=>#, ->#, A]): ProdCat[==>, -->, A, A] =
//        ProdCat.id[==>, =>#, -->, ->#, A](C, A.first, D, A.second)
//      def andThen[X, Y, Z](ab: ProdCat[==>, -->, X, Y], bc: ProdCat[==>, -->, Y, Z]): ProdCat[==>, -->, X, Z] =
//        ab.andThen(bc)
//    }
//
//  implicit def categorySameTC[==>[_,_], -->[_,_], TC0[_]](implicit
//    C: Subcat.Aux[==>, TC0],
//    D: Subcat.Aux[-->, TC0]
//  ): Subcat.Aux[ProdCat[==>, -->, *, *], TC0] =
//      new Subcat[ProdCat[==>, -->, *, *]] {
//        type TC[a] = TC0[a]
//        def id[A](implicit A: TC[A]) = ProdCat.id[==>, TC, -->, TC, A](C, A, D, A)
//        def andThen[A, B, C](ab: ProdCat[==>, -->, A, B], bc: ProdCat[==>, -->, B, C]) =
//          ab.andThen(bc)
//      }
//
//  implicit def monoidalSameTC[==>[_,_], -->[_,_], TC0[_], P[_,_], I](implicit
//    m1: Cartesian.Aux[==>, P, TC0, I],
//    m2: Cartesian.Aux[-->, P, TC0, I],
//  ): Cartesian.Aux[ProdCat[==>, -->, *, *], P, TC0, I] =
//    new Cartesian[ProdCat[==>, -->, *, *], P] {
//      type Id = I
//      type TC[a] = TC0[a]
//      def idl[A]: ProdCat[==>, -->, P[I, A], A] = ProdCat(m1.idl, m2.idl)
//      def coidl[A]: ProdCat[==>, -->, A, P[I, A]] = ProdCat(m1.coidl, m2.coidl)
//      def idr[A]: ProdCat[==>, -->, P[A, I], A] = ProdCat(m1.idr, m2.idr)
//      def coidr[A]: ProdCat[==>, -->, A, P[A, I]] = ProdCat(m1.coidr, m2.coidr)
//      def C: Subcat.Aux[ProdCat[==>, -->, *, *], TC0] = categorySameTC[==>, -->, TC0](m1.C, m2.C)
//      def bifunctor: Endobifunctor[ProdCat[==>, -->, *, *], P] = new Endobifunctor[ProdCat[==>, -->, *, *], P] {
//        val L, R, C = categorySameTC[==>, -->, TC0](m1.C, m2.C)
//        def leftMap [A, B, Z](fn:  ProdCat[==>, -->, A, Z]): ProdCat[==>, -->, P[A, B], P[Z, B]] =
//          ProdCat(m1.bifunctor.leftMap(fn.first), m2.bifunctor.leftMap(fn.second))
//        def rightMap[A, B, Z](fn:  ProdCat[==>, -->, B, Z]): ProdCat[==>, -->, P[A, B], P[A, Z]] =
//          ProdCat(m1.bifunctor.rightMap(fn.first), m2.bifunctor.rightMap(fn.second))
//      }
//      def associate[X, Y, Z]: ProdCat[==>, -->, P[P[X, Y], Z], P[X, P[Y, Z]]] = ProdCat(m1.associate, m2.associate)
//      def diassociate[X, Y, Z]: ProdCat[==>, -->, P[X, P[Y, Z]], P[P[X, Y], Z]] = ProdCat(m1.diassociate, m2.diassociate)
//      def fst[A, B]: ProdCat[==>, -->, P[A, B], A] = ProdCat(m1.fst, m2.fst)
//      def snd[A, B]: ProdCat[==>, -->, P[A, B], B] = ProdCat(m1.snd, m2.snd)
//      def diag[A]: ProdCat[==>, -->, A, P[A, A]] = ProdCat(m1.diag, m2.diag)
//      def &&&[X, Y, Z](f: ProdCat[==>, -->, X, Y], g: ProdCat[==>, -->, X, Z]): ProdCat[==>, -->, X, P[Y, Z]] =
//        ProdCat(m1.&&&(f.first, g.first), m2.&&&(f.second, g.second))
//      def braid[A, B]: ProdCat[==>, -->, P[A, B], P[B, A]] = ProdCat(m1.braid, m2.braid)
//    }

}
