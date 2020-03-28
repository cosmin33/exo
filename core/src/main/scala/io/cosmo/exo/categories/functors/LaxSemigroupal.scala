package io.cosmo.exo.categories.functors

import cats._
import io.cosmo.exo.categories._
import io.cosmo.exo._

trait LaxSemigroupal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends Exofunctor[==>, -->, F]  {
  type TC[_]

  def M1: Associative.Aux[==>, ⊙=, TC]
  def M2: Associative.Aux[-->, ⊙-, λ[a => TC[F[a]]]]

  def product[A, B]: (F[A] ⊙- F[B]) => F[A ⊙= B]

  def map2[A, B, C](fn: (A ⊙= B) ==> C)(implicit E: Exo.Con[* => *, * --> F[C]]): (F[A] ⊙- F[B]) --> F[C] =
    E.map(Dual(product[A, B]))(map[A ⊙= B, C](fn))

  def preserveSemigroup[M](ma: CSemigroup.Aux[==>, ⊙=, TC, M])(implicit
    E: Exo.Con[* => *, * --> F[M]]
  ): CSemigroup.Aux[-->, ⊙-, λ[a => TC[F[a]]], F[M]] =
    CSemigroup.unsafe(E.map(Dual(product[M, M]))(map(ma.op)))(M2)

}

object LaxSemigroupal extends LaxSemigroupalInstances {
  type Aux[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], =>#[_], F[_]] = LaxSemigroupal[==>, ⊙=, -->, ⊙-, F] {type TC[a] = =>#[a]}

  type Endo[->[_, _], ⊙[_, _], F[_]] = LaxSemigroupal[->, ⊙, ->, ⊙, F]
  // TODO: compose cu alte LaxMonoidal de diverse feluri (vezi cats)
  // TODO: daca am LaxSemigroupal[->] atunci am si LaxSemigroupal[Dicat[->]], iar daca il am pe asta am si LaxSemigroupal[Iso[->]].. (ca si la Exofunctor)

  abstract class ProtoFunctor[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](F: Exofunctor[==>, -->, F]) extends LaxSemigroupal[==>, ⊙=, -->, ⊙-, F] {
    def map[A, B](f: A ==> B) = F.map(f)
  }



}

import LaxSemigroupalHelpers._

trait LaxSemigroupalInstances extends LaxSemigroupalInstances01 {
  implicit def importApply[F[_]](implicit a: Apply[F]): LaxSemigroupal.Endo[* => *, (*, *), F] =
    new LaxSemigroupal.Endo[* => *, (*, *), F] with ImportApply[F] {val F = a}
  implicit def importConSemi[F[_]](implicit cs: ContravariantSemigroupal[F]): LaxSemigroupal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] =
    new LaxSemigroupal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] with ImportConSemi[F] {val F = cs}
}

trait LaxSemigroupalInstances01 extends LaxSemigroupalInstances02 {
  implicit def importInvSemi[F[_]](implicit is: InvariantSemigroupal[F]): LaxSemigroupal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] =
    new LaxSemigroupal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] with ImportInvSemi[F] {val F = is}
}

trait LaxSemigroupalInstances02 extends LaxSemigroupalInstances03{
  implicit def importApplicative[F[_]](implicit a: Applicative[F]): LaxMonoidal.Endo[* => *, (*, *), F] =
    new LaxMonoidal.Endo[* => *, (*, *), F] with ImportApplicative[F] {val F = a}

  implicit def importContravariantMonoidal[F[_]](implicit cm: ContravariantMonoidal[F]): LaxMonoidal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] =
    new LaxMonoidal[Dual[* => *,*,*], (*, *), * => *, (*, *), F] with ImportConMono[F] {val F = cm}
}

trait LaxSemigroupalInstances03 extends LaxSemigroupalInstances04 {
  implicit def importInvariantMonoidal[F[_]](implicit im: InvariantMonoidal[F]): LaxMonoidal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] =
    new LaxMonoidal[Dicat[* => *,*,*], (*, *), * => *, (*, *), F] with ImportInvMono[F] {val F = im}
}

trait LaxSemigroupalInstances04 extends LaxSemigroupalInstances05 {
//  implicit def invToIso[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], =>#[_], F[_]](implicit
//    l: LaxSemigroupal.Aux[Dicat[==>,*,*], ⊙=, -->, ⊙-, =>#, F]
//  ): LaxSemigroupal.Aux[Iso[==>,*,*], ⊙=, -->, ⊙-, =>#, F] =
//    new LaxSemigroupal[Iso[==>,*,*], ⊙=, -->, ⊙-, F] {
//      type TC[a] = =>#[a]
//      def M1 = {
//        val x: Associative.Aux[Iso[==>,*,*], ⊙=, =>#] = Iso.isoAssoc(l.M1, l.M1.bifunctor)
//        ???
//      }
//      def M2 = l.M2
//      def map[A, B](i: Iso[==>, A, B]) = l.map((i.to, Dual(i.from)))
//      def product[A, B]: (F[A] ⊙- F[B]) => F[A ⊙= B] = ???
//    }

}

trait LaxSemigroupalInstances05 {

}

private object LaxSemigroupalHelpers {
  trait ImportSemigroupal[F[_]] {
    protected def F: InvariantSemigroupal[F]
    type TC[a] = Trivial.T1[a]
    def product[A, B]: ((F[A], F[B])) => F[(A, B)] = { case (fa, fb) => F.product(fa, fb) }
    def M2: Associative.Aux[* => *, (*, *), λ[a => Trivial.T1[F[a]]]] = Associative[* => *, (*, *)]
  }

  trait ImportApply[F[_]] extends ImportSemigroupal[F] {
    def F: Apply[F]
    def M1 = implicitly[Monoidal.Aux[* => *, (*, *), Trivial.T1, Unit]]
    def map[A, B](f: A => B): F[A] => F[B] = F.map(_)(f)
  }

  trait ImportConSemi[F[_]] extends ImportSemigroupal[F] {
    def F: ContravariantSemigroupal[F]
    def M1 = implicitly[Monoidal.Aux[Dual[* => *,*,*], (*, *), Trivial.T1, Unit]]
    def map[A, B](f: Dual[* => *, A, B]): F[A] => F[B] = F.contramap(_)(f)
  }

  trait ImportInvSemi[F[_]] extends ImportSemigroupal[F] {
    def F: InvariantSemigroupal[F]
    def M1 = implicitly[Monoidal.Aux[Dicat[* => *,*,*], (*, *), Trivial.T1, Unit]]
    def map[A, B](f: Dicat[* => *, A, B]): F[A] => F[B] = F.imap(_)(f._1)(f._2)
  }

  trait ImportMonoidal[F[_]] extends ImportSemigroupal[F] {
    protected def F: InvariantMonoidal[F]
    type I = Unit
    override def M2: Monoidal.Aux[* => *, (*, *), λ[a => Trivial.T1[F[a]]], F[Unit]] =
      new Monoidal.ProtoAssociative[* => *, (*, *), λ[a => Trivial.T1[F[a]]]](Associative[* => *, (*, *)]) {
        type Id = F[Unit]
        def idl  [A]: ((Id, A)) => A = _._2
        def coidl[A]: A => (Id, A)   = (F.unit, _)
        def idr  [A]: ((A, Id)) => A = _._1
        def coidr[A]: A => (A, Id)   = (_, F.unit)
      }
  }

  trait ImportApplicative[F[_]] extends ImportMonoidal[F] with ImportApply[F] {
    def F: Applicative[F]
  }
  trait ImportConMono[F[_]] extends ImportMonoidal[F] with ImportConSemi[F] {
    def F: ContravariantMonoidal[F]
  }
  trait ImportInvMono[F[_]] extends ImportMonoidal[F] with ImportInvSemi[F] {
    def F: InvariantMonoidal[F]
  }

  trait InvToIso[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]]

}