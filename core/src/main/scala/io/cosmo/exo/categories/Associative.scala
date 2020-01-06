package io.cosmo.exo.categories

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.categories.functors.{Endobifunctor, Exobifunctor}

import scala.{:: => _}

trait Associative[->[_, _], ⊙[_, _]] {
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor.Aux[->, TC, ⊙]

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
    bif: Endobifunctor.Aux[->, Tc, ⊙]
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

  val cocartesianFn1Disj: Cartesian.Aux[Opp[* => *]#l, \/, Trivial.T1, Void] =
      new Cartesian.Proto[Opp[* => *]#l, \/, Trivial.T1, Void] {
        def C: Subcat.AuxT[Opp[* => *]#l] = Semicategory.function1OppCat
        def bifunctor = Exobifunctor.oppEndobifunctor
        def diassociate[X, Y, Z]: (X \/ Y \/ Z) => (X \/ (Y \/ Z)) =
          _.fold(xy => xy.fold(_.left[Y \/ Z], _.left[Z].right[X]),
                  z => z.right[Y].right[X])
        def associate  [X, Y, Z]: (X \/ (Y \/ Z)) => (X \/ Y \/ Z) =
          _.fold(x => x.left[Y].left[Z],
                yz => yz.fold(_.right[X].left[Z], _.right[X \/ Y]))
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
