package io.cosmo.exo.categories

import cats.Inject
import cats.implicits._
import io.cosmo.exo
import io.cosmo.exo._
import io.cosmo.exo.categories.Cartesian.Aux
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.categories.functors.{Endobifunctor, Exobifunctor}

import scala.{:: => _}

trait Associative[->[_, _], ⊙[_, _]] {
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [X, Y, Z]: ⊙[⊙[X, Y], Z] -> ⊙[X, ⊙[Y, Z]]
  def diassociate[X, Y, Z]: ⊙[X, ⊙[Y, Z]] -> ⊙[⊙[X, Y], Z]

  private type <->[a, b] = Iso[->, a, b]
  def isoAssociate[X, Y, Z]: ⊙[⊙[X, Y], Z] <-> ⊙[X, ⊙[Y, Z]] = Iso.unsafe(associate[X,Y,Z], diassociate[X,Y,Z])(C)
}

object Associative extends AssociativeImplicits {
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Associative[->, ⊙] {type TC[a] = TC0[a]}
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Associative[->, ⊙] { type TC[A] = TC0[A] }

  def fromIso[->[_,_], ⊙[_,_], Tc[_]](i: ∀∀∀[λ[(a,b,c) => Iso[->, ⊙[⊙[a, b], c], ⊙[a, ⊙[b, c]]]]])(implicit
    cat: Subcat.Aux[->, Tc],
    bif: Endobifunctor[->, ⊙]
  ): Associative.Aux[->, ⊙, Tc] = new Associative[->, ⊙] {
    type TC[a] = Tc[a]
    val C = cat
    val bifunctor = bif
    def associate  [X, Y, Z] = i.apply[X, Y, Z].to
    def diassociate[X, Y, Z] = i.apply[X, Y, Z].from
  }

  def apply[->[_,_], ⊙[_,_]](implicit assoc: Associative[->, ⊙]): Associative.Aux[->, ⊙, assoc.TC] = assoc

}

trait AssociativeImplicits extends AssociativeImplicits01 {
  val cartesianFn1Tuple: Cartesian.Aux[Function1, Tuple2, Trivial.T1, Unit] =
      new Cartesian.Proto[Function1, Tuple2, Trivial.T1, Unit] {
        type ->[a, b] = a => b
        def C: Subcat.AuxT[* => *] = Semicategory.function1
        def bifunctor = Exobifunctor.tuple2Endobifunctor
        def associate  [X, Y, Z]: ((X, Y), Z) -> (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
        def diassociate[X, Y, Z]: (X, (Y, Z)) -> ((X, Y), Z) = { case (x, (y, z)) => ((x, y), z) }
        def braid[A, B]: ((A, B)) => (B, A) = { case (a, b) => (b, a) }
        def coidl[A]: A -> (Unit, A) = a => ((), a)
        def coidr[A]: A -> (A, Unit) = a => (a, ())
        def idr[A]: (A, Unit) -> A = { case (a, _) => a }
        def idl[A]: (Unit, A) -> A = { case (_, a) => a }
        def fst[A, B]: (A, B) -> A = { case (a, _) => a }
        def snd[A, B]: (A, B) -> B = { case (_, b) => b }
        def &&&[X, Y, Z](f: X -> Y, g: X -> Z): X -> (Y, Z) = x => (f(x), g(x))
        def diag[A]: A -> (A, A) = a => (a, a)
        override def pair[A, B, X, Y](f: A => B, g: X => Y): ((A, X)) => (B, Y) =
          {case (a, x) => (f(a), g(x))} // override for performance
      }

  implicit def impCartesianFn1Tuple: Cartesian.Aux[Function1, Tuple2, Trivial.T1, Unit] = cartesianFn1Tuple

  implicit def cartesianFn1Conj: Cartesian.Aux[* => *, /\, T1, Unit] =
    /\.leibniz.subst[Cartesian.Aux[* => *, *[_,_], Trivial.T1, Unit]](cartesianFn1Tuple)

  implicit val cocartesianFn1Disj: Cartesian.Aux[Opp[* => *]#l, \/, Trivial.T1, Void] =
      new Cartesian.Proto[Opp[* => *]#l, \/, Trivial.T1, Void] {
        def C: Subcat.AuxT[Opp[* => *]#l] = DualModule.oppSubcat(implicitly[Subcat.Aux[* => *, Trivial.T1]])
        def bifunctor = DualModule.oppEndobifunctor(Endobifunctor[* => *, \/])
        def diassociate[X, Y, Z]: (X \/ Y \/ Z) => (X \/ (Y \/ Z)) = _.fold(_.fold(_.left[Y \/ Z], _.left[Z].right[X]), _.right[Y].right[X])
        def associate  [X, Y, Z]: (X \/ (Y \/ Z)) => (X \/ Y \/ Z) = _.fold(_.left[Y].left[Z], _.fold(_.right[X].left[Z], _.right[X \/ Y]))
        def braid[A, B]: (B \/ A) => (A \/ B) = _.fold(_.right, _.left)
        def coidr[A]: (A \/ Void) => A = _.fold[A](identity, identity)
        def coidl[A]: (Void \/ A) => A = _.fold[A](identity, identity)
        def idl[A]: A => (Void \/ A) = _.right
        def idr[A]: A => (A \/ Void) = _.left
        def fst[A, B]: A => (A \/ B) = _.left
        def snd[A, B]: B => (A \/ B) = _.right
        def diag[A]: (A \/ A) => A = _.fold[A](identity, identity)
        def &&&[X, Y, Z](f: Y => X, g: Z => X): (Y \/ Z) => X = _.fold(f, g)
        //// overrides for performance
        override def pair[A, B, X, Y](f: B => A, g: Y => X): (B \/ Y) => (A \/ X) = _.fold(f(_).left, g(_).right)
      }

  def cocartesianFn1Either: Cartesian.Aux[Opp[* => *]#l, Either, Trivial.T1, Void] =
    \/.leibniz.flip.subst[Cartesian.Aux[Opp[* => *]#l, *[_,_], Trivial.T1, Void]](cocartesianFn1Disj)

  implicit def cocartesianFn1EitherDual: Cartesian.Aux[Dual[* => *,*,*], Either, Trivial.T1, Void] =
    Dual.leibniz[* => *].subst[Cartesian.Aux[*[_,_], Either, Trivial.T1, Void]](cocartesianFn1Either)

  implicit def cocartesianFn1DisjDual: Cartesian.Aux[Dual[* => *,*,*], \/, Trivial.T1, Void] =
    Dual.leibniz[* => *].subst[Cartesian.Aux[*[_,_], \/, Trivial.T1, Void]](cocartesianFn1Disj)

  implicit val injMonoidalDisj: Monoidal[Inject, \/] with Symmetric[Inject, \/] =
    new Monoidal[Inject, \/] with Symmetric[Inject, \/] {
      type Id = Void
      type TC[a] = Trivial.T1[a]
      def C: Subcat.Aux[Inject, Trivial.T1] = Semicategory.injSubcat
      def idl[A]: Inject[Void \/ A, A] = new Inject[Void \/ A, A] {
        def inj: Void \/ A => A = _.fold(identity, identity)
        def prj: A => Option[Void \/ A] = ???
      }
      def coidl[A]: Inject[A, Void \/ A] = ???
      def idr[A]: Inject[A \/ Void, A] = ???
      def coidr[A]: Inject[A, A \/ Void] = ???
      def bifunctor: Endobifunctor[Inject, \/] = ???
      def braid[A, B]: Inject[A \/ B, B \/ A] = ???
      def associate[X, Y, Z]: Inject[X \/ Y \/ Z, X \/ (Y \/ Z)] = ???
      def diassociate[X, Y, Z]: Inject[X \/ (Y \/ Z), X \/ Y \/ Z] = ???
    }



  //  val injMonoidal: Cartesian[Inject, (*, *)] =
  //    new Cartesian[Inject, (*, *)] {
  implicit val injMonoidalTuple: Monoidal[Inject, (*, *)] with Symmetric[Inject, (*, *)] =
    new Monoidal[Inject, (*, *)] with Symmetric[Inject, (*, *)] {
      type Id = Unit
      type TC[a] = Trivial.T1[a]

      def C: Subcat.Aux[Inject, Trivial.T1] = Semicategory.injSubcat

      def idl[A]: Inject[(Unit, A), A] = new Inject[(Unit, A), A] {
        val inj: ((Unit, A)) => A = _._2
        val prj: A => Option[(Unit, A)] = a => ((), a).some
      }

      def coidl[A]: Inject[A, (Unit, A)] = new Inject[A, (Unit, A)] {
        val inj: A => (Unit, A) = ((), _)
        val prj: ((Unit, A)) => Option[A] = _._2.some
      }

      def idr[A]: Inject[(A, Unit), A] = new Inject[(A, Unit), A] {
        val inj: ((A, Unit)) => A = _._1
        val prj: A => Option[(A, Unit)] = a => (a, ()).some
      }

      def coidr[A]: Inject[A, (A, Unit)] = new Inject[A, (A, Unit)] {
        val inj: A => (A, Unit) = (_, ())
        val prj: ((A, Unit)) => Option[A] = _._1.some
      }

      def bifunctor: Endobifunctor[Inject, (*, *)] = new Endobifunctor[Inject, (*, *)] {
        val L, R, C = Semicategory.injSubcat
        def leftMap [A, B, Z](fn:  Inject[A, Z]): Inject[(A, B), (Z, B)] =
          new Inject[(A, B), (Z, B)] {
            val inj: ((A, B)) => (Z, B) = { case (a, b) => (fn(a), b) }
            val prj: ((Z, B)) => Option[(A, B)] = { case (z, b) => fn.prj(z).map((_, b)) }
          }
        def rightMap[A, B, Z](fn:  Inject[B, Z]): Inject[(A, B), (A, Z)] =
          new Inject[(A, B), (A, Z)] {
            val inj: ((A, B)) => (A, Z) = { case (a, b) => (a, fn(b)) }
            val prj: ((A, Z)) => Option[(A, B)] = { case (a, z) => fn.prj(z).map((a, _)) }
          }
      }

      def associate[X, Y, Z]: Inject[((X, Y), Z), (X, (Y, Z))] = new Inject[((X, Y), Z), (X, (Y, Z))] {
        val inj: (((X, Y), Z)) => (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
        val prj: ((X, (Y, Z))) => Option[((X, Y), Z)] = { case (x, (y, z)) => ((x, y), z).some }
      }

      def diassociate[X, Y, Z]: Inject[(X, (Y, Z)), ((X, Y), Z)] = new Inject[(X, (Y, Z)), ((X, Y), Z)] {
        val inj: ((X, (Y, Z))) => ((X, Y), Z) = { case (x, (y, z)) => ((x, y), z) }
        val prj: (((X, Y), Z)) => Option[(X, (Y, Z))] = { case ((x, y), z) => (x, (y, z)).some }
      }

      def braid[A, B]: Inject[(A, B), (B, A)] = new Inject[(A, B), (B, A)] {
        val inj: ((A, B)) => (B, A) = { case (a, b) => (b, a) }
        val prj: ((B, A)) => Option[(A, B)] = { case (b, a) => (a, b).some }
      }

      //      def fst[A, B]: Inject[(A, B), A] = new Inject[(A, B), A] {
      //        val inj: ((A, B)) => A = _._1
      //        val prj: A => Option[(A, B)] = _ => None
      //      }
      //      def snd[A, B]: Inject[(A, B), B] = new Inject[(A, B), B] {
      //        val inj: ((A, B)) => B = _._2
      //        val prj: B => Option[(A, B)] = _ => None
      //      }
      //      def diag[A]: Inject[A, (A, A)] = new Inject[A, (A, A)] {
      //        val inj: A => (A, A) = a => (a, a)
      //        val prj: ((A, A)) => Option[A] = _._1.some
      //      }
      //      def &&&[X, Y, Z](f: Inject[X, Y], g: Inject[X, Z]): Inject[X, (Y, Z)] =
      //        new Inject[X, (Y, Z)] {
      //          val inj: X => (Y, Z) = x => (f(x), g(x))
      //          val prj: ((Y, Z)) => Option[X] = { case (y, z) => f.prj(y) orElse g.prj(z) }
      //        }
      //      override def pair[A, B, X, Y](f: A Inject B, g: X Inject Y): (A, X) Inject (B, Y) =
      //        new Inject[(A, X), (B, Y)] {
      //          val inj: ((A, X)) => (B, Y) = { case (a, x) => (f(a), g(x)) }
      //          val prj: ((B, Y)) => Option[(A, X)] = { case (b, y) => f.prj(b) zip g.prj(y) }
      //        }

    }

}
trait AssociativeImplicits01 extends AssociativeImplicits02 {
}
trait AssociativeImplicits02 {
}

//trait HAssociative[->[_,_], HList, :::[_, _ <: HList] <: HList, Nil <: HList] {
//  type TC[_]
//  def C: Category.Aux[->, TC]
//  //def bifunctor: Bifunctor.Endo[:::, ->, TC]
//
//  def associate  [X, Y, Z]: :::[:::[X, Y], Z] -> :::[X, :::[Y, Z]]
//  def diassociate[X, Y, Z]: :::[X, :::[Y, Z]] -> :::[:::[X, Y], Z]
//
//}

//trait AssociativeK[->[_[_],_[_]], ⊙[_[_],_[_],_]] {
//  type TC[_[_]]
//  def C: CategoryK.Aux[->, TC]
//  def bifunctor: BifunctorK.Aux1[⊙, ->, TC]
//
//  def associate  [X[_], Y[_], Z[_]]: ⊙[⊙[X, Y, ?], Z, ?] -> ⊙[X, ⊙[Y, Z, ?], ?]
//  def diassociate[X[_], Y[_], Z[_]]: ⊙[X, ⊙[Y, Z, ?], ?] -> ⊙[⊙[X, Y, ?], Z, ?]
//}
//object AssociativeK {
//  trait Aux[->[_[_],_[_]], ⊙[_[_],_[_],_], TC0[_[_]]] extends AssociativeK[->, ⊙] {
//    type TC[f[_]] = TC0[f]
//  }
//}
