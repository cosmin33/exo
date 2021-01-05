package io.cosmo.exo.categories.functors

import cats._
import cats.implicits._
import io.cosmo.exo.categories._
import io.cosmo.exo._

trait LaxSemigroupal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends Exofunctor[==>, -->, F]  { self =>
  type TC1[_]
  type TC2[_]
  def M1: Associative.Aux[==>, ⊙=, TC1]
  def M2: Associative.Aux[-->, ⊙-, TC2]

  // (F[A], F[B]) => F[(A, B)]
  def product[A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B]

  def map2[A, B, C](fn: (A ⊙= B) ==> C): (F[A] ⊙- F[B]) --> F[C] = M2.C.andThen(product[A, B], map(fn))

  def preserveCSemigroup[M](ma: CSemigroup.Aux[==>, ⊙=, TC1, M]): CSemigroup.Aux[-->, ⊙-, TC2, F[M]] =
    CSemigroup.unsafe1(map2(ma.op))(M2)

  def compose[~~>[_,_], ⊙~[_,_], ~>#[_], G[_]](G: LaxSemigroupal.Aux[-->, ⊙-, ~~>, ⊙~, TC2, ~>#, G]
  ) =
    new LaxSemigroupal[==>, ⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] {
      type TC1[a] = self.TC1[a]
      type TC2[a] = ~>#[a]
      def M1: Associative.Aux[==>, ⊙=, TC1] = self.M1
      def M2: Associative.Aux[~~>, ⊙~, TC2] = G.M2
      def product[A, B]: G[F[A]] ⊙~ G[F[B]] ~~> G[F[A ⊙= B]] = M2.C.andThen(G.product[F[A], F[B]], G.map(self.product[A, B]))
      def map[A, B](f: A ==> B): G[F[A]] ~~> G[F[B]] = G.map(self.map(f))
    }
}

object LaxSemigroupal extends LaxSemigroupalInstances {
  type Aux[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], =>#[_], ->#[_], F[_]] =
    LaxSemigroupal[==>, ⊙=, -->, ⊙-, F] { type TC1[a] = =>#[a]; type TC2[a] = ->#[a] }

  type Endo[->[_, _], ⊙[_, _], F[_]] = LaxSemigroupal[->, ⊙, ->, ⊙, F]

  abstract class ProtoFunctor[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](F: Exofunctor[==>, -->, F]) extends LaxSemigroupal[==>, ⊙=, -->, ⊙-, F] {
    def map[A, B](f: A ==> B) = F.map(f)
  }

  implicit def orderTest: LaxSemigroupal.Aux[Dual[* => *, *, *], \/, * => *, /\, Trivial.T1, Trivial.T1, Order] =
    new LaxSemigroupal[Dual[* => *,*,*], \/, * => *, /\, Order] {
      type TC1[a] = Trivial.T1[a]
      type TC2[a] = Trivial.T1[a]
      def M1: Associative.Aux[Dual[* => *,*,*], \/, TC1] = implicitly
      def M2: Associative.Aux[* => *, /\, TC2] = implicitly
      def product[A, B]: Order[A] /\ Order[B] => Order[A \/ B] = { p =>
        implicit val (oa1, ob1) = (p._1, p._2)
        Order[\/[A, B]]
      }
      def map[A, B](f: Dual[* => *, A, B]): Order[A] => Order[B] = Contravariant[Order].contramap(_)(f)
      //override def map2[A, B, C](fn: Dual[* => *, A \/ B, C]): Order[A] /\ Order[B] => Order[C] = super.map2(fn)
    }

}

import LaxSemigroupalHelpers._

trait LaxSemigroupalInstances extends LaxSemigroupalInstances01 {
  implicit def importApply[F[_]](implicit a: Apply[F]): LaxSemigroupal.Endo[* => *, (*, *), F] =
    new ImportApply[F] {val F = a}
  implicit def importConSemi[F[_]](implicit cs: ContravariantSemigroupal[F]): LaxSemigroupal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] =
    new ImportConSemi[F] {val F = cs}
}

trait LaxSemigroupalInstances01 extends LaxSemigroupalInstances02 {
  implicit def importInvSemi[F[_]](implicit is: InvariantSemigroupal[F]): LaxSemigroupal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] =
    new ImportInvSemi[F] {val F = is}
}

trait LaxSemigroupalInstances02 extends LaxSemigroupalInstances03{
  implicit def importApplicative[F[_]](implicit a: Applicative[F]): LaxMonoidal.Endo[* => *, (*, *), F] =
    new ImportApplicative[F] {val F = a}

  implicit def importContravariantMonoidal[F[_]](implicit cm: ContravariantMonoidal[F]): LaxMonoidal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] =
    new ImportConMono[F] {val F = cm}
}

trait LaxSemigroupalInstances03 extends LaxSemigroupalInstances04 {
  implicit def importInvariantMonoidal[F[_]](implicit im: InvariantMonoidal[F]): LaxMonoidal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] =
    new ImportInvMono[F] {val F = im}
}

trait LaxSemigroupalInstances04 extends LaxSemigroupalInstances05 {
}

trait LaxSemigroupalInstances05 {

}

private object LaxSemigroupalHelpers {
  trait ImportSemigroupal[F[_]] {
    protected def F: InvariantSemigroupal[F]
    type TC1[a] = Trivial.T1[a]
    type TC2[a] = Trivial.T1[a]
    def product[A, B]: ((F[A], F[B])) => F[(A, B)] = { case (fa, fb) => F.product(fa, fb) }
    def M2: Associative.Aux[* => *, (*, *), λ[a => Trivial.T1[F[a]]]] = Associative[* => *, (*, *)]
  }

  trait ImportApply[F[_]] extends ImportSemigroupal[F] with LaxSemigroupal.Endo[* => *, (*, *), F] {
    def F: Apply[F]
    def M1 = implicitly[Monoidal.Aux[* => *, (*, *), Trivial.T1, Unit]]
    def map[A, B](f: A => B): F[A] => F[B] = F.map(_)(f)
  }

  trait ImportConSemi[F[_]] extends ImportSemigroupal[F] with LaxSemigroupal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] {
    def F: ContravariantSemigroupal[F]
    def M1 = implicitly[Monoidal.Aux[Dual[* => *,*,*], (*, *), Trivial.T1, Unit]]
    def map[A, B](f: Dual[* => *, A, B]): F[A] => F[B] = F.contramap(_)(f)
  }

  trait ImportInvSemi[F[_]] extends ImportSemigroupal[F] with LaxSemigroupal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] {
    def F: InvariantSemigroupal[F]
    def M1 = implicitly[Monoidal.Aux[Dicat[* => *,*,*], (*, *), Trivial.T1, Unit]]
    def map[A, B](f: Dicat[* => *, A, B]): F[A] => F[B] = F.imap(_)(f._1)(f._2)
  }

  trait ImportMonoidal[F[_]] extends ImportSemigroupal[F] {
    protected def F: InvariantMonoidal[F]
    type I = Unit
    def id: I => F[I] = F.point(_)
    override def M2: Monoidal.Aux[* => *, (*, *), λ[a => Trivial.T1[F[a]]], F[Unit]] =
      new Monoidal.ProtoFromAssociative[* => *, (*, *), λ[a => Trivial.T1[F[a]]]](Associative[* => *, (*, *)]) {
        type Id = F[Unit]
        def idl  [A: TC]: ((Id, A)) => A = _._2
        def coidl[A: TC]: A => (Id, A)   = (F.unit, _)
        def idr  [A: TC]: ((A, Id)) => A = _._1
        def coidr[A: TC]: A => (A, Id)   = (_, F.unit)
      }
  }

  trait ImportApplicative[F[_]] extends ImportMonoidal[F] with ImportApply[F] with LaxMonoidal.Endo[* => *, (*, *), F] {
    def F: Applicative[F]
  }
  trait ImportConMono[F[_]] extends ImportMonoidal[F] with ImportConSemi[F] with LaxMonoidal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] {
    def F: ContravariantMonoidal[F]
  }
  trait ImportInvMono[F[_]] extends ImportMonoidal[F] with ImportInvSemi[F] with LaxMonoidal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] {
    def F: InvariantMonoidal[F]
  }


}