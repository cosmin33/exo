package io.cosmo.exo.categories.data

import cats.Monad
import io.cosmo.exo.categories.{Cartesian, HasTerminalObject, Kleis}
import io.cosmo.exo.evidence.{===, Is}

trait KleisModule {
  type Type[->[_,_], F[_], A, B] <: A -> F[B]
  def leibniz[->[_,_], F[_], A, B]: (A -> F[B]) === Type[->, F, A, B]
}

private[exo] object KleisModuleImpl extends KleisModule {
  type Type[->[_,_], F[_], A, B] = A -> F[B]
  def leibniz[->[_,_], F[_], A, B] = Is.refl
}

object KleisModule {
  implicit def conversion[->[_,_], F[_], A, B](fn: A -> F[B]): Kleis[->, F, A, B] = Kleis.leibniz(fn)

  def kleisCartesian[->[_,_], P[_,_], F[_], Term](implicit
    c1: Cartesian[->, P],
    t: HasTerminalObject[->],
    F: Monad[F],
  ): Cartesian[Kleis[->, F, *, *], P] = {
    new Cartesian[Kleis[->, F, *, *], P] {
      type TC[a] = c1.TC[a]
      type Id = t.Terminal
      def fst[A, B]: Kleis[->, F, P[A, B], A] = {
        val r1: P[A, B] -> A = c1.fst[A, B]

        //: P[A, B] -> F[A]
        ???
      }
      def snd[A, B] = ???
      def diag[A] = ???
      def &&&[X, Y, Z](f: Kleis[->, F, X, Y], g: Kleis[->, F, X, Z]) = ???
      def braid[A, B] = ???
      def idl[A] = ???
      def coidl[A] = ???
      def idr[A] = ???
      def coidr[A] = ???
      def C = ???
      def bifunctor = ???
      def associate[X, Y, Z] = ???
      def diassociate[X, Y, Z] = ???
    }
    ???
  }
}