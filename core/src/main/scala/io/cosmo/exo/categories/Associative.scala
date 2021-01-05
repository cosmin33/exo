package io.cosmo.exo.categories

import cats.Inject
import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories.Trivial.trivialInstance
import io.cosmo.exo.categories.functors.{Endobifunctor, Exo, Exobifunctor}

import scala.{:: => _}

trait Associative[->[_, _], ⊙[_, _]] {
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [X: TC, Y: TC, Z: TC]: ⊙[⊙[X, Y], Z] -> ⊙[X, ⊙[Y, Z]]
  def diassociate[X: TC, Y: TC, Z: TC]: ⊙[X, ⊙[Y, Z]] -> ⊙[⊙[X, Y], Z]

  def grouped[A, B, X, Y](f: A -> B, g: X -> Y): ⊙[A, X] -> ⊙[B, Y] = bifunctor.bimap(f, g)

  private type <->[a, b] = Iso[->, a, b]
  def isoAssociator[X: TC, Y: TC, Z: TC]: ⊙[⊙[X, Y], Z] <-> ⊙[X, ⊙[Y, Z]] = Iso.unsafe(associate[X,Y,Z], diassociate[X,Y,Z])(C)
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
    def associate  [X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].to
    def diassociate[X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].from
  }

  def apply[->[_,_], ⊙[_,_]](implicit assoc: Associative[->, ⊙]): Associative.Aux[->, ⊙, assoc.TC] = assoc

  def dual[->[_,_], ⊙[_,_], T[_]](a: Associative.Aux[->, ⊙, T]): Associative.Aux[Dual[->,*,*], ⊙, T] =
    new Associative[Dual[->,*,*], ⊙] {
      type TC[a] = T[a]
      def C: Subcat.Aux[Dual[->, *, *], T] = a.C.dual
      def bifunctor: Endobifunctor[Dual[->, *, *], ⊙] = Exobifunctor.dual(a.bifunctor)
      def associate  [X: TC, Y: TC, Z: TC] = Dual(a.diassociate)
      def diassociate[X: TC, Y: TC, Z: TC] = Dual(a.associate)
    }

}

trait AssociativeImplicits extends AssociativeImplicits01 {
  val cartesianFn1Tuple: Cartesian.Aux[* => *, Tuple2, Trivial.T1, Unit] =
      new Cartesian[* => *, Tuple2] {
        type TC[a] = Trivial.T1[a]
        type Id = Unit
        private type ->[a, b] = a => b
        def C: Subcat.AuxT[* => *] = Semicategory.function1
        def bifunctor = Exobifunctor.tuple2Endobifunctor
        def associate  [X: Trivial.T1, Y: Trivial.T1, Z: Trivial.T1]: ((X, Y), Z) -> (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
        def diassociate[X: Trivial.T1, Y: Trivial.T1, Z: Trivial.T1]: (X, (Y, Z)) -> ((X, Y), Z) = { case (x, (y, z)) => ((x, y), z) }
        def braid[A: TC, B: TC]: ((A, B)) => (B, A) = { case (a, b) => (b, a) }
        def coidl[A: TC]: A -> (Unit, A) = a => ((), a)
        def coidr[A: TC]: A -> (A, Unit) = a => (a, ())
        def idr[A: TC]: (A, Unit) -> A = { case (a, _) => a }
        def idl[A: TC]: (Unit, A) -> A = { case (_, a) => a }
        def fst[A: TC, B: TC]: (A, B) -> A = { case (a, _) => a }
        def snd[A: TC, B: TC]: (A, B) -> B = { case (_, b) => b }
        def &&&[X, Y, Z](f: X -> Y, g: X -> Z): X -> (Y, Z) = x => (f(x), g(x))
        def diag[A: TC]: A -> (A, A) = a => (a, a)
        override def grouped[A, B, X, Y](f: A => B, g: X => Y): ((A, X)) => (B, Y) =
          {case (a, x) => (f(a), g(x))} // override for performance
      }

  implicit def impCartesianFn1Tuple: Cartesian.Aux[Function1, Tuple2, Trivial.T1, Unit] = cartesianFn1Tuple

  implicit def cartesianFn1Conj: Cartesian.Aux[* => *, /\, Trivial.T1, Unit] =
    /\.leibniz.subst[Cartesian.Aux[* => *, *[_,_], Trivial.T1, Unit]](cartesianFn1Tuple)

  implicit val cocartesianFn1Disj: Cartesian.Aux[Opp[* => *]#l, \/, Trivial.T1, Void] =
      new Cartesian[Opp[* => *]#l, \/] {
        type TC[a] = Trivial.T1[a]
        type Id = Void
        def C: Subcat.AuxT[Opp[* => *]#l] = DualModule.oppSubcat(implicitly[Subcat.Aux[* => *, Trivial.T1]])
        def bifunctor = DualModule.oppEndobifunctor(Endobifunctor[* => *, \/])
        def diassociate[X: Trivial.T1, Y: Trivial.T1, Z: Trivial.T1]: (X \/ Y \/ Z) => (X \/ (Y \/ Z)) = _.fold(_.fold(_.left[Y \/ Z], _.left[Z].right[X]), _.right[Y].right[X])
        def associate  [X: Trivial.T1, Y: Trivial.T1, Z: Trivial.T1]: (X \/ (Y \/ Z)) => (X \/ Y \/ Z) = _.fold(_.left[Y].left[Z], _.fold(_.right[X].left[Z], _.right[X \/ Y]))
        def braid[A: TC, B: TC]: (B \/ A) => (A \/ B) = _.fold(_.right, _.left)
        def coidr[A: TC]: (A \/ Void) => A = _.fold[A](identity, identity)
        def coidl[A: TC]: (Void \/ A) => A = _.fold[A](identity, identity)
        def idl[A: TC]: A => (Void \/ A) = _.right
        def idr[A: TC]: A => (A \/ Void) = _.left
        def fst[A: TC, B: TC]: A => (A \/ B) = _.left
        def snd[A: TC, B: TC]: B => (A \/ B) = _.right
        def diag[A: TC]: (A \/ A) => A = _.fold[A](identity, identity)
        def &&&[X, Y, Z](f: Y => X, g: Z => X): (Y \/ Z) => X = _.fold(f, g)
        //// overrides for performance
        override def grouped[A, B, X, Y](f: B => A, g: Y => X): (B \/ Y) => (A \/ X) = _.fold(f(_).left, g(_).right)
      }

  implicit val assocFn1Disj: Associative.Aux[* => *, \/, Trivial.T1] =
    new Associative[* => *, \/] {
      type TC[a] = Trivial.T1[a]
      def C = implicitly
      def bifunctor = implicitly
      def associate  [X: TC, Y: TC, Z: TC]: X \/ Y \/ Z => X \/ (Y \/ Z) = cocartesianFn1Disj.diassociate(trivialInstance, trivialInstance, trivialInstance)
      def diassociate[X: TC, Y: TC, Z: TC]: X \/ (Y \/ Z) => X \/ Y \/ Z = cocartesianFn1Disj.associate(trivialInstance, trivialInstance, trivialInstance)
    }

  def cocartesianFn1Either: Cartesian.Aux[Opp[* => *]#l, Either, Trivial.T1, Void] =
    \/.leibniz.flip.subst[Cartesian.Aux[Opp[* => *]#l, *[_,_], Trivial.T1, Void]](cocartesianFn1Disj)

  implicit def cocartesianFn1EitherDual: Cartesian.Aux[Dual[* => *,*,*], Either, Trivial.T1, Void] =
    Dual.leibniz[* => *].subst[Cartesian.Aux[*[_,_], Either, Trivial.T1, Void]](cocartesianFn1Either)

  implicit def cocartesianFn1DisjDual: Cartesian.Aux[Dual[* => *,*,*], \/, Trivial.T1, Void] =
    Dual.leibniz[* => *].subst[Cartesian.Aux[*[_,_], \/, Trivial.T1, Void]](cocartesianFn1Disj)

  val injMonoidalDisj: Monoidal[Opp[Inject]#l, \/] with Symmetric[Opp[Inject]#l, \/] =
    new Monoidal[Opp[Inject]#l, \/] with Symmetric[Opp[Inject]#l, \/] {
      override type Id = Void
      override type TC[a] = Trivial.T1[a]
      override def idl[A: TC]: Inject[A, Void \/ A] = new Inject[A, Void \/ A] {
        val inj: A => Void \/ A = _.right[Void]
        val prj: Void \/ A => Option[A] = _.fold(_ => Option.empty[A], _.some)
      }
      override def coidl[A: TC]: Inject[Void \/ A, A] = new Inject[Void \/ A, A] {
        val inj: Void \/ A => A = _.fold(v => v, a => a)
        val prj: A => Option[Void \/ A] = _.right[Void].some
      }
      override def idr[A: TC]: Inject[A, A \/ Void] = new Inject[A, A \/ Void] {
        val inj: A => A \/ Void = _.left[Void]
        val prj: A \/ Void => Option[A] = _.fold(_.some, _ => Option.empty[A])
      }
      override def coidr[A: TC]: Inject[A \/ Void, A] = new Inject[A \/ Void, A] {
        val inj: A \/ Void => A = _.fold(a => a, v => v)
        val prj: A => Option[A \/ Void] = _.left[Void].some
      }
      override def braid[A: TC, B: TC]: Inject[B \/ A, A \/ B] = new Inject[B \/ A, A \/ B] {
        val inj: B \/ A => A \/ B = _.swap
        val prj: A \/ B => Option[B \/ A] = _.swap.some
      }
      def C: Subcat.Aux[Opp[Inject]#l, Trivial.T1] = DualModule.oppSubcat(implicitly[Subcat.Aux[Inject, Trivial.T1]])
      def bifunctor: Endobifunctor[Opp[Inject]#l, \/] = new Endobifunctor[Opp[Inject]#l, \/] {
        override def bimap[A, X, B, Y](left: Inject[X, A], right: Inject[Y, B]): Inject[X \/ Y, A \/ B] = ???
      }
      def associate  [X: TC, Y: TC, Z: TC]: Inject[X \/ (Y \/ Z), X \/ Y \/ Z] = ???
      def diassociate[X: TC, Y: TC, Z: TC]: Inject[X \/ Y \/ Z, X \/ (Y \/ Z)] = ???
    }

  implicit val injMonoidalTuple: Monoidal.Aux[Inject, (*, *), Trivial.T1, Unit] with Symmetric.Aux[Inject, (*, *), Trivial.T1] =
    new Monoidal[Inject, (*, *)] with Symmetric[Inject, (*, *)] {
      type Id = Unit
      type TC[a] = Trivial.T1[a]

      def C: Subcat.Aux[Inject, Trivial.T1] = Semicategory.injSubcat

      def idl[A: TC]: Inject[(Unit, A), A] = new Inject[(Unit, A), A] {
        val inj: ((Unit, A)) => A = _._2
        val prj: A => Option[(Unit, A)] = a => ((), a).some
      }

      def coidl[A: TC]: Inject[A, (Unit, A)] = new Inject[A, (Unit, A)] {
        val inj: A => (Unit, A) = ((), _)
        val prj: ((Unit, A)) => Option[A] = _._2.some
      }

      def idr[A: TC]: Inject[(A, Unit), A] = new Inject[(A, Unit), A] {
        val inj: ((A, Unit)) => A = _._1
        val prj: A => Option[(A, Unit)] = a => (a, ()).some
      }

      def coidr[A: TC]: Inject[A, (A, Unit)] = new Inject[A, (A, Unit)] {
        val inj: A => (A, Unit) = (_, ())
        val prj: ((A, Unit)) => Option[A] = _._1.some
      }

      def bifunctor: Endobifunctor[Inject, (*, *)] = new Endobifunctor[Inject, (*, *)] {
        override def bimap[A, X, B, Y](left: Inject[A, X], right: Inject[B, Y]): Inject[(A, B), (X, Y)] =
          new Inject[(A, B), (X, Y)] {
            val inj: ((A, B)) => (X, Y)         = ab => (left(ab._1), right(ab._2))
            val prj: ((X, Y)) => Option[(A, B)] = xy => left.prj(xy._1) zip right.prj(xy._2)
          }
      }

      def associate[X: TC, Y: TC, Z: TC]: Inject[((X, Y), Z), (X, (Y, Z))] = new Inject[((X, Y), Z), (X, (Y, Z))] {
        val inj: (((X, Y), Z)) => (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
        val prj: ((X, (Y, Z))) => Option[((X, Y), Z)] = { case (x, (y, z)) => ((x, y), z).some }
      }

      def diassociate[X: TC, Y: TC, Z: TC]: Inject[(X, (Y, Z)), ((X, Y), Z)] = new Inject[(X, (Y, Z)), ((X, Y), Z)] {
        val inj: ((X, (Y, Z))) => ((X, Y), Z) = { case (x, (y, z)) => ((x, y), z) }
        val prj: (((X, Y), Z)) => Option[(X, (Y, Z))] = { case ((x, y), z) => (x, (y, z)).some }
      }

      def braid[A: TC, B: TC]: Inject[(A, B), (B, A)] = new Inject[(A, B), (B, A)] {
        val inj: ((A, B)) => (B, A) = { case (a, b) => (b, a) }
        val prj: ((B, A)) => Option[(A, B)] = { case (b, a) => (a, b).some }
      }

    }

}
trait AssociativeImplicits01 extends AssociativeImplicits02 {
}
trait AssociativeImplicits02 {
}
