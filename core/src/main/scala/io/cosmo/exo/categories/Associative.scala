package io.cosmo.exo.categories

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories.functors.{Endobifunctor, Exobifunctor}

import scala.{:: => _}

trait Associative[->[_, _], ⊙[_, _]] {
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor.Aux[->, TC, ⊙]

  def associate  [X, Y, Z]: ⊙[⊙[X, Y], Z] -> ⊙[X, ⊙[Y, Z]]
  def diassociate[X, Y, Z]: ⊙[X, ⊙[Y, Z]] -> ⊙[⊙[X, Y], Z]

  private type <->[a, b] = Iso.Aux[->, TC, a, b]
  def isoCanonic[X, Y, Z]: ⊙[⊙[X, Y], Z] <-> ⊙[X, ⊙[Y, Z]] =
    Iso.unsafe[->, ⊙[⊙[X, Y], Z], ⊙[X, ⊙[Y, Z]], TC](associate[X,Y,Z], diassociate[X,Y,Z])(C)
}

object Associative extends AssociativeImplicits {
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Associative[->, ⊙] {type TC[a] = TC0[a]}
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Associative[->, ⊙] { type TC[A] = TC0[A] }

  private[categories] trait Impl[->[_, _], ⊙[_, _], C[_]] extends Associative[->, ⊙] {
    protected def source: Associative.Aux[->, ⊙, C]
    override type TC[a] = C[a]
    override def C = source.C
    override def bifunctor = source.bifunctor
    override def associate[X, Y, Z] = source.associate
    override def diassociate[X, Y, Z] = source.diassociate
  }

  def apply[->[_,_], ⊙[_,_]](implicit assoc: Associative[->, ⊙]): Associative.Aux[->, ⊙, assoc.TC] = assoc

}

trait AssociativeImplicits extends AssociativeImplicits01 {
  implicit def cartesianFn1Tuple: Cartesian.Aux[Function1, Tuple2, Trivial.T1, Unit] =
      new Cartesian.Proto[Function1, Tuple2, Trivial.T1, Unit] {
        type ->[a, b] = a => b
        def C: Subcat.AuxT[* => *] = Semicategory.function1
        def bifunctor = Exobifunctor.tuple2Endobifunctor
        def associate[X, Y, Z]: ((X, Y), Z) -> (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
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

  implicit def cocartesianFn1EitherDual: Cartesian.Aux[Dual[* => *,*,*], Either, Trivial.T1, Void] =
    Dual.leibniz2[* => *].flip.subst[Cartesian.Aux[*[_,_], Either, Trivial.T1, Void]](cocartesianFn1Either)

  implicit def cocartesianFn1Either: Cartesian.Aux[Opp[* => *]#l, Either, Trivial.T1, Void] =
      new Cartesian.Proto[Opp[* => *]#l, Either, Trivial.T1, Void] {
        def C: Subcat.AuxT[Opp[* => *]#l] = Semicategory.function1OppCat
        def bifunctor = Exobifunctor.eitherOppEndoBifunctor
        def diassociate[X, Y, Z]: Either[Either[X, Y], Z] => Either[X, Either[Y, Z]] = {
          case Left(xy) => xy.fold(_.asLeft[Either[Y,Z]], _.asLeft[Z].asRight[X])
          case Right(z) => z.asRight[Y].asRight[X]
        }
        def associate[X, Y, Z]: Either[X, Either[Y, Z]] => Either[Either[X, Y], Z] = {
          case Left(x) => x.asLeft[Y].asLeft[Z]
          case Right(yz) => yz.fold(_.asRight[X].asLeft[Z], _.asRight[Either[X, Y]])
        }
        def braid[A, B]: Either[B, A] => Either[A, B] = _.fold(_.asRight, _.asLeft)
        def coidr[A]: Either[A, Void] => A = _.fold[A](identity, identity)
        def coidl[A]: Either[Void, A] => A = _.fold[A](identity, identity)
        def idl[A]: A => Either[Void, A] = _.asRight
        def idr[A]: A => Either[A, Void] = _.asLeft
        def fst[A, B]: A => Either[A, B] = _.asLeft
        def snd[A, B]: B => Either[A, B] = _.asRight
        def diag[A]: Either[A, A] => A = _.fold[A](identity, identity)
        def &&&[X, Y, Z](f: Y => X, g: Z => X): Either[Y, Z] => X = _.fold(f, g)
        // override for performance
        override def pair[A, B, X, Y](f: B => A, g: Y => X): Either[B, Y] => Either[A, X] =
          _.fold(f(_).asLeft, g(_).asRight)
      }


  def cocartesianFn1Disj(implicit
    bi: Endobifunctor.Aux[Opp[* => *]#l, Trivial.T1, \/]
  ): Cartesian.Aux[Opp[* => *]#l, \/, Trivial.T1, Void] =
      new Cartesian.Proto[Opp[* => *]#l, \/, Trivial.T1, Void] {
        def C: Subcat.AuxT[Opp[* => *]#l] = Semicategory.function1OppCat
        def bifunctor = bi
        def diassociate[X, Y, Z]: (X \/ Y \/ Z) => (X \/ (Y \/ Z)) =
          _.fold(xy => xy.fold(_.left[Y \/ Z], _.left[Z].right[X]),
                  z => z.right[Y].right[X])
        def associate[X, Y, Z]: (X \/ (Y \/ Z)) => (X \/ Y \/ Z) =
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
