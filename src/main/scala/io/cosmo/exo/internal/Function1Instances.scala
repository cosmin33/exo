package io.cosmo.exo.internal

import io.cosmo.exo.*
import io.cosmo.exo.syntax.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.{Endobifunctor, *}
import io.cosmo.exo.internal.any.*
import io.cosmo.exo.categories.*

trait Function1SemicategoryInstances extends Function1SemicategoryInstances01 {
  given function1Distributive1: Distributive.Aux[Function, Trivial, Tuple2, Unit, Either, Void] =
    new Distributive[Function, Tuple2, Either] {
      type TC[a] = Trivial[a]
      type ⊙[a, b] = (a, b)
      type Id = Unit
      type ProductId = Unit
      type SumId = Void
      def id[A: TC]: A => A = identity
      def andThen[A, B, C](ab: A => B, bc: B => C): A => C = bc.compose(ab)
      def cartesian = summon
      def cocartesian = summon
      def distribute[A: Trivial, B: Trivial, C: Trivial] = (a, bc) => bc.fold((a, _).asLeft, (a, _).asRight)
    }
}

trait Function1SemicategoryInstances01 {
  given function1Distributive2: Distributive.Aux[Function, Trivial, /\, Unit, \/, Void] =
    IsK2.lower2[[f[_, _], g[_, _]] =>> Distributive.Aux[Function, Trivial, f, Unit, g, Void]]
      .on(/\.unsafeLeibniz, \/.unsafeLeibniz)(Semicategory.function1Distributive1)
}

trait Function1InitialTerminalInstances {
  given function1Terminal: Terminal.Aux[Function, Trivial, Unit] =
    new Terminal.Proto[Function, Trivial, Unit]:
      def TC: Trivial[Unit] = Trivial[Unit]
      def subcat: Subcat.AuxT[Dual[Function,*,*]] = summon
      def terminate[A: TC]: A => Unit = _ => ()

  given function1Initial: Initial.Aux[Function, Trivial, Void] =
    new Initial.Proto[Function, Trivial, Void]:
      def TC: Trivial[Void] = Trivial[Void]
      def subcat: Subcat.AuxT[Function] = summon
      def initiate[A: TC]: Void => A = Void.absurd
}

trait Function1AssociativeInstances {
  given cccFn1Tuple: Ccc.Aux[Function, Tuple2, Trivial, Unit, Function] =
    new Ccc.Proto[Function, Tuple2, Trivial, Unit, Function] {
      private type ->[a, b] = a => b
      def C: Subcat.AuxT[Function] = summon
      def bifunctor = Exobifunctor.tuple2
      def associate  [X: TC, Y: TC, Z: TC]: ((X, Y), Z) -> (X, (Y, Z)) = { case ((x, y), z) => (x, (y, z)) }
      def diassociate[X: TC, Y: TC, Z: TC]: (X, (Y, Z)) -> ((X, Y), Z) = { case (x, (y, z)) => ((x, y), z) }
      def braid[A: TC, B: TC]: ((A, B)) => (B, A) = (a, b) => (b, a)
      def coidl[A: TC]: A -> (Unit, A) = a => ((), a)
      def coidr[A: TC]: A -> (A, Unit) = a => (a, ())
      def idr[A: TC]: (A, Unit) -> A = (a, _) => a
      def idl[A: TC]: (Unit, A) -> A = (_, a) => a
      def fst[A: TC, B: TC]: (A, B) -> A = (a, _) => a
      def snd[A: TC, B: TC]: (A, B) -> B = (_, b) => b
      def &&&[A, B, C](f: A -> B, g: A -> C): A -> (B, C) = x => (f(x), g(x))
      def diag[A: TC]: A -> (A, A) = a => (a, a)
      def curry[X, Y, Z](f: ((X, Y)) => Z): X => (Y => Z) = x => y => f((x, y))
      def uncurry[X, Y, Z](f: X => (Y => Z)): ((X, Y)) => Z = (x, y) => f(x)(y)
      override def apply[A, B](using TC[A |-> B]): ((A => B, A)) => B = (ab, a) => ab(a)
    }

  given cartesianFn1Conj: Ccc.Aux[Function, /\, Trivial, Unit, Function] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> Ccc.Aux[Function, f, Trivial, Unit, Function]](cccFn1Tuple)

  given cocartesianFn1Disj: Cartesian.Aux[Opp[Function], \/, Trivial, Void] =
    new Cartesian.Proto[Opp[* => *], \/, Trivial, Void] {
      def C: Subcat.AuxT[Opp[* => *]] = Semicategory.oppSubcat(using summon)
      def bifunctor = Exobifunctor.oppEndobifunctor(using \/.bifunctor)
      def associate  [X: TC, Y: TC, Z: TC]: (X \/ (Y \/ Z)) => (X \/ Y \/ Z) = _.fold(_.left[Y].left[Z], _.fold(_.right[X].left[Z], _.right[X \/ Y]))
      def diassociate[X: TC, Y: TC, Z: TC]: (X \/ Y \/ Z) => (X \/ (Y \/ Z)) = _.fold(_.fold(_.left[Y \/ Z], _.left[Z].right[X]), _.right[Y].right[X])
      def braid[A: TC, B: TC]: (B \/ A) => (A \/ B) = _.fold(_.right, _.left)
      def coidr[A: TC]: (A \/ Void) => A = _.fold[A](identity[A], identity[A])
      def coidl[A: TC]: (Void \/ A) => A = _.fold[A](identity[A], identity[A])
      def idl[A: TC]: A => (Void \/ A) = _.right
      def idr[A: TC]: A => (A \/ Void) = _.left
      def fst[A: TC, B: TC]: A => (A \/ B) = _.left
      def snd[A: TC, B: TC]: B => (A \/ B) = _.right
      def diag[A: TC]: (A \/ A) => A = _.fold[A](identity, identity)
      def &&&[X, A, B](f: A => X, g: B => X): (A \/ B) => X = _.fold(f, g)
    }

  given cocartesianFn1Either: Cartesian.Aux[Opp[Function], Either, Trivial, Void] =
    \/.unsafeLeibniz.flip.subst[[f[_,_]] =>> Cartesian.Aux[Opp[Function], f, Trivial, Void]](cocartesianFn1Disj)

  given cocartesianFn1DisjDual: Cartesian.Aux[Dual[Function,*,*], \/, Trivial, Void] =
    Dual.leibniz[Function].subst[[f[_,_]] =>> Cartesian.Aux[f, \/, Trivial, Void]](cocartesianFn1Disj)

  given cocartesianFn1EitherDual: Cartesian.Aux[Dual[Function,*,*], Either, Trivial, Void] =
    Dual.leibniz[Function].subst[[f[_,_]] =>> Cartesian.Aux[f, Either, Trivial, Void]](cocartesianFn1Either)

}
