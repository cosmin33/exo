package io.cosmo.exo.categories

import cats.Inject
import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories.Trivial.trivial
import io.cosmo.exo.categories.functors.{Endobifunctor, Exobifunctor}

trait Associative[->[_, _], ⊙[_, _]] {
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [X: TC, Y: TC, Z: TC]: ⊙[⊙[X, Y], Z] -> ⊙[X, ⊙[Y, Z]]
  def diassociate[X: TC, Y: TC, Z: TC]: ⊙[X, ⊙[Y, Z]] -> ⊙[⊙[X, Y], Z]

  def grouped[A, B, X, Y](f: A -> B, g: X -> Y): ⊙[A, X] -> ⊙[B, Y] = bifunctor.bimap(f, g)

  def strongFirst [A, B, C: TC](fa: A -> B): ⊙[C, A] -> ⊙[C, B] = grouped(C.id[C], fa)
  def strongSecond[A, B, C: TC](fa: A -> B): ⊙[A, C] -> ⊙[B, C] = grouped(fa, C.id[C])

  private type <->[a, b] = Iso[->, a, b]
  def isoAssociator[X: TC, Y: TC, Z: TC]: ⊙[⊙[X, Y], Z] <-> ⊙[X, ⊙[Y, Z]] = Iso.unsafe(associate[X,Y,Z], diassociate[X,Y,Z])(C)
}

object Associative extends AssociativeImplicits {
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Associative[->, ⊙] {type TC[a] = TC0[a]}
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Associative[->, ⊙] { type TC[A] = TC0[A] }

  def fromIso[->[_,_], ⊙[_,_], Tc[_]](i: ∀∀∀[λ[(a,b,c) => Iso[->, ⊙[⊙[a, b], c], ⊙[a, ⊙[b, c]]]]])(implicit
    cat: Subcat.Aux[->, Tc],
    bif: Endobifunctor[->, ⊙]
  ): Associative.Aux[->, ⊙, Tc] = new Associative.Proto[->, ⊙, Tc] {
    val C = cat
    val bifunctor = bif
    def associate  [X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].to
    def diassociate[X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].from
  }

  def apply[->[_,_], ⊙[_,_]](implicit assoc: Associative[->, ⊙]): Associative.Aux[->, ⊙, assoc.TC] = assoc

  def dualdual[->[_,_], ⊙[_,_], T[_]](a: Associative.Aux[Dual[->,*,*], ⊙, T]): Associative.Aux[->, ⊙, T] =
    //TODO: remove asInstanceOf and use DualModule.doubleDualIsK2 once is repaired
    dual(a).asInstanceOf[Associative.Aux[->, ⊙, T]]

  def dual[->[_,_], ⊙[_,_], T[_]](a: Associative.Aux[->, ⊙, T]): Associative.Aux[Dual[->,*,*], ⊙, T] =
    new Associative.Proto[Dual[->,*,*], ⊙, T] {
      def C: Subcat.Aux[Dual[->, *, *], T] = a.C.dual
      def bifunctor: Endobifunctor[Dual[->, *, *], ⊙] = Exobifunctor.dual(a.bifunctor)
      def associate  [X: TC, Y: TC, Z: TC] = Dual(a.diassociate)
      def diassociate[X: TC, Y: TC, Z: TC] = Dual(a.associate)
    }

}

trait AssociativeImplicits extends AssociativeImplicits01 {
  def cartesianFn1Tuple: Cartesian.Aux[* => *, Tuple2, Trivial.T1, Unit] =
      new Cartesian[* => *, Tuple2] {
        type TC[a] = Trivial.T1[a]
        type Id = Unit
        private type ->[a, b] = a => b
        def C: Subcat.AuxT[* => *] = Semicategory.function1
        def bifunctor = Exobifunctor.tuple2Endobifunctor
        def associate  [X: TC, Y: TC, Z: TC]: ((X, Y), Z) -> (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
        def diassociate[X: TC, Y: TC, Z: TC]: (X, (Y, Z)) -> ((X, Y), Z) = { case (x, (y, z)) => ((x, y), z) }
        def braid[A: TC, B: TC]: ((A, B)) => (B, A) = { case (a, b) => (b, a) }
        def coidl[A: TC]: A -> (Unit, A) = a => ((), a)
        def coidr[A: TC]: A -> (A, Unit) = a => (a, ())
        def idr[A: TC]: (A, Unit) -> A = { case (a, _) => a }
        def idl[A: TC]: (Unit, A) -> A = { case (_, a) => a }
        def fst[A: TC, B: TC]: (A, B) -> A = { case (a, _) => a }
        def snd[A: TC, B: TC]: (A, B) -> B = { case (_, b) => b }
        def &&&[A, B, C](f: A -> B, g: A -> C): A -> (B, C) = x => (f(x), g(x))
        def diag[A: TC]: A -> (A, A) = a => (a, a)
      }

  implicit def impCartesianFn1Tuple: Cartesian.Aux[* => *, Tuple2, Trivial.T1, Unit] = cartesianFn1Tuple

  implicit def cartesianFn1Conj: Cartesian.Aux[* => *, /\, Trivial.T1, Unit] =
    /\.leibniz.subst[Cartesian.Aux[* => *, *[_,_], Trivial.T1, Unit]](cartesianFn1Tuple)

  implicit def cocartesianFn1Disj: Cartesian.Aux[Opp[* => *]#l, \/, Trivial.T1, Void] =
      new Cartesian[Opp[* => *]#l, \/] {
        type TC[a] = Trivial.T1[a]
        type Id = Void
        def C: Subcat.AuxT[Opp[* => *]#l] = DualModule.oppSubcat(implicitly[Subcat.Aux[* => *, Trivial.T1]])
        def bifunctor = DualModule.oppEndobifunctor(Endobifunctor[* => *, \/])
        def diassociate[X: TC, Y: TC, Z: TC]: (X \/ Y \/ Z) => (X \/ (Y \/ Z)) = _.fold(_.fold(_.left[Y \/ Z], _.left[Z].right[X]), _.right[Y].right[X])
        def associate  [X: TC, Y: TC, Z: TC]: (X \/ (Y \/ Z)) => (X \/ Y \/ Z) = _.fold(_.left[Y].left[Z], _.fold(_.right[X].left[Z], _.right[X \/ Y]))
        def braid[A: TC, B: TC]: (B \/ A) => (A \/ B) = _.fold(_.right, _.left)
        def coidr[A: TC]: (A \/ Void) => A = _.fold[A](identity, identity)
        def coidl[A: TC]: (Void \/ A) => A = _.fold[A](identity, identity)
        def idl[A: TC]: A => (Void \/ A) = _.right
        def idr[A: TC]: A => (A \/ Void) = _.left
        def fst[A: TC, B: TC]: A => (A \/ B) = _.left
        def snd[A: TC, B: TC]: B => (A \/ B) = _.right
        def diag[A: TC]: (A \/ A) => A = _.fold[A](identity, identity)
        def &&&[X, A, B](f: A => X, g: B => X): (A \/ B) => X = _.fold(f, g)
      }

  implicit def assocFn1Disj: Associative.Aux[* => *, \/, Trivial.T1] =
    new Associative[* => *, \/] {
      type TC[a] = Trivial.T1[a]
      def C = implicitly
      def bifunctor = implicitly
      def associate  [X: TC, Y: TC, Z: TC]: X \/ Y \/ Z => X \/ (Y \/ Z) = cocartesianFn1Disj.diassociate(trivial, trivial, trivial)
      def diassociate[X: TC, Y: TC, Z: TC]: X \/ (Y \/ Z) => X \/ Y \/ Z = cocartesianFn1Disj.associate(trivial, trivial, trivial)
    }
  implicit def assocFn1Eith: Associative.Aux[* => *, Either, Trivial.T1] =
    \/.leibniz.flip.subst[Associative.Aux[* => *, *[_,_], Trivial.T1]](assocFn1Disj)

  def cocartesianFn1Either: Cartesian.Aux[Opp[* => *]#l, Either, Trivial.T1, Void] =
    \/.leibniz.flip.subst[Cartesian.Aux[Opp[* => *]#l, *[_,_], Trivial.T1, Void]](cocartesianFn1Disj)

  implicit def cocartesianFn1EitherDual: Cartesian.Aux[Dual[* => *,*,*], Either, Trivial.T1, Void] =
    Dual.leibniz[* => *].subst[Cartesian.Aux[*[_,_], Either, Trivial.T1, Void]](cocartesianFn1Either)

  implicit def cocartesianFn1DisjDual: Cartesian.Aux[Dual[* => *,*,*], \/, Trivial.T1, Void] =
    Dual.leibniz[* => *].subst[Cartesian.Aux[*[_,_], \/, Trivial.T1, Void]](cocartesianFn1Disj)

  private type >->[A, B] = Inject[A, B]

  implicit def injMonoidalTuple: Monoidal.Aux[Inject, (*, *), Trivial.T1, Unit] with Symmetric.Aux[Inject, (*, *), Trivial.T1] =
    new Monoidal[Inject, (*, *)] with Symmetric[Inject, (*, *)] {
      type Id = Unit
      type TC[a] = Trivial.T1[a]
      def C: Subcat.Aux[>->, Trivial.T1] = Semicategory.injSubcat
      def idl[A: TC]: >->[(Unit, A), A] = new >->[(Unit, A), A] {
        val inj: ((Unit, A)) => A = _._2
        val prj: A => Option[(Unit, A)] = a => ((), a).some
      }
      def coidl[A: TC]: >->[A, (Unit, A)] = new >->[A, (Unit, A)] {
        val inj: A => (Unit, A) = ((), _)
        val prj: ((Unit, A)) => Option[A] = _._2.some
      }
      def idr[A: TC]: >->[(A, Unit), A] = new >->[(A, Unit), A] {
        val inj: ((A, Unit)) => A = _._1
        val prj: A => Option[(A, Unit)] = a => (a, ()).some
      }
      def coidr[A: TC]: >->[A, (A, Unit)] = new >->[A, (A, Unit)] {
        val inj: A => (A, Unit) = (_, ())
        val prj: ((A, Unit)) => Option[A] = _._1.some
      }
      def bifunctor: Endobifunctor[>->, (*, *)] = new Endobifunctor[>->, (*, *)] {
        override def bimap[A, X, B, Y](left: >->[A, X], right: >->[B, Y]): >->[(A, B), (X, Y)] =
          new >->[(A, B), (X, Y)] {
            val inj: ((A, B)) => (X, Y)         = ab => (left(ab._1), right(ab._2))
            val prj: ((X, Y)) => Option[(A, B)] = xy => left.prj(xy._1) zip right.prj(xy._2)
          }
      }
      def associate[X: TC, Y: TC, Z: TC]: >->[((X, Y), Z), (X, (Y, Z))] = new >->[((X, Y), Z), (X, (Y, Z))] {
        val inj: (((X, Y), Z)) => (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
        val prj: ((X, (Y, Z))) => Option[((X, Y), Z)] = { case (x, (y, z)) => ((x, y), z).some }
      }
      def diassociate[X: TC, Y: TC, Z: TC]: >->[(X, (Y, Z)), ((X, Y), Z)] = new >->[(X, (Y, Z)), ((X, Y), Z)] {
        val inj: ((X, (Y, Z))) => ((X, Y), Z) = { case (x, (y, z)) => ((x, y), z) }
        val prj: (((X, Y), Z)) => Option[(X, (Y, Z))] = { case ((x, y), z) => (x, (y, z)).some }
      }
      def braid[A: TC, B: TC]: >->[(A, B), (B, A)] = new >->[(A, B), (B, A)] {
        val inj: ((A, B)) => (B, A) = { case (a, b) => (b, a) }
        val prj: ((B, A)) => Option[(A, B)] = { case (b, a) => (a, b).some }
      }

    }

  implicit def injMonoidalDisj: Cartesian.Aux[Opp[Inject]#l, \/, Trivial.T1, Void] =
    new Cartesian[Opp[Inject]#l, \/] {
      override type Id = Void
      override type TC[a] = Trivial.T1[a]
      def C: Subcat.Aux[Opp[>->]#l, Trivial.T1] = DualModule.oppSubcat(implicitly[Subcat.Aux[>->, Trivial.T1]])
      override def idl[A: TC]: >->[A, Void \/ A] = new >->[A, Void \/ A] {
        val inj: A => Void \/ A = _.right[Void]
        val prj: Void \/ A => Option[A] = _.fold(_ => none[A], _.some)
      }
      override def coidl[A: TC]: >->[Void \/ A, A] = new >->[Void \/ A, A] {
        val inj: Void \/ A => A = _.fold(v => v, a => a)
        val prj: A => Option[Void \/ A] = _.right[Void].some
      }
      override def idr[A: TC]: >->[A, A \/ Void] = new >->[A, A \/ Void] {
        val inj: A => A \/ Void = _.left[Void]
        val prj: A \/ Void => Option[A] = _.fold(_.some, _ => none[A])
      }
      override def coidr[A: TC]: >->[A \/ Void, A] = new >->[A \/ Void, A] {
        val inj: A \/ Void => A = _.fold(a => a, v => v)
        val prj: A => Option[A \/ Void] = _.left[Void].some
      }
      override def braid[A: TC, B: TC]: >->[B \/ A, A \/ B] = new >->[B \/ A, A \/ B] {
        val inj: B \/ A => A \/ B = _.swap
        val prj: A \/ B => Option[B \/ A] = _.swap.some
      }
      def bifunctor: Endobifunctor[Opp[>->]#l, \/] = new Endobifunctor[Opp[>->]#l, \/] {
        override def bimap[A, X, B, Y](left: >->[X, A], right: >->[Y, B]): >->[X \/ Y, A \/ B] =
          new >->[X \/ Y, A \/ B] {
            def inj: X \/ Y => A \/ B = _.fold(x => -\/(left.inj(x)), y => \/-(right.inj(y)))
            def prj: A \/ B => Option[X \/ Y] = _.fold(a => left.prj(a).map(-\/[X, Y]), b => right.prj(b).map(\/-[X, Y]))
          }
      }
      def associate  [X: TC, Y: TC, Z: TC]: >->[X \/ (Y \/ Z), X \/ Y \/ Z] =
        new >->[X \/ (Y \/ Z), X \/ Y \/ Z] {
          def inj: X \/ (Y \/ Z) => X \/ Y \/ Z = cocartesianFn1Disj.associate[X, Y, Z](trivial, trivial, trivial)
          def prj: X \/ Y \/ Z => Option[X \/ (Y \/ Z)] =
            xyz => cocartesianFn1Disj.diassociate[X, Y, Z](trivial, trivial, trivial)(xyz).some
        }
      def diassociate[X: TC, Y: TC, Z: TC]: >->[X \/ Y \/ Z, X \/ (Y \/ Z)] =
        new >->[X \/ Y \/ Z, X \/ (Y \/ Z)] {
          def inj: X \/ Y \/ Z => X \/ (Y \/ Z) = cocartesianFn1Disj.diassociate[X, Y, Z](trivial, trivial, trivial)
          def prj: X \/ (Y \/ Z) => Option[X \/ Y \/ Z] =
            xyz => cocartesianFn1Disj.associate[X, Y, Z](trivial, trivial, trivial)(xyz).some
        }
      override def fst[A: TC, B: TC]: >->[A, A \/ B] =
        new >->[A, A \/ B] {
          def inj: A => A \/ B = _.left[B]
          def prj: A \/ B => Option[A] = _.fold(_.some, _ => none[A])
        }
      override def snd[A: TC, B: TC]: >->[B, A \/ B] =
        new >->[B, A \/ B] {
          def inj: B => A \/ B = _.right[A]
          def prj: A \/ B => Option[B] = _.fold(_ => none[B], _.some)
        }
      override def diag[A: TC]: >->[A \/ A, A] =
        new >->[A \/ A, A] {
          def inj: A \/ A => A = _.fold(identity, identity)
          def prj: A => Option[A \/ A] = _.left[A].some
        }
      override def &&&[A, B, C](f: >->[B, A], g: >->[C, A]): >->[B \/ C, A] =
        new >->[B \/ C, A] {
          def inj: B \/ C => A = _.fold(f.inj, g.inj)
          def prj: A => Option[B \/ C] = a => f.prj(a).map(_.left[C]) orElse g.prj(a).map(_.right[B])
        }
    }

}
trait AssociativeImplicits01 extends AssociativeImplicits02 {
}
trait AssociativeImplicits02 {
}
