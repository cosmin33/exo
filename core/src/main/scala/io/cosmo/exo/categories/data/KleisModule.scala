package io.cosmo.exo.categories.data

import cats.{Id, Monad}
import io.cosmo.exo.categories.Subcat.Aux
import io.cosmo.exo.categories.{Cartesian, Endobifunctor, Terminal, Kleis, Opp, Subcat}
import io.cosmo.exo.evidence.{===, Is}
import io.cosmo.exo.categories.functors._

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

  def kleisCartesian[->[_,_], ⨂[_,_], F[_], Term](implicit
    cc: Cartesian[->, ⨂],
    term: Terminal.AuxTerm[->, Term],
    mon: Exomonad[->, Id, F],
  ): Cartesian[λ[(a,b) => a -> F[b]], ⨂] = {
    new Cartesian[λ[(a,b) => a -> F[b]], ⨂] {
      type TC[a] = cc.TC[a]
      type Id = term.Terminal

      override def &&&[X, Y, Z](f: X -> F[Y], g: X -> F[Z]): X -> F[Y ⨂ Z] = {
        val x: X -> (F[Y] ⨂ F[Z]) = cc.&&&(f, g)

        ???
      }


      override def fst[A, B]: ⨂[A, B] -> F[A] = cc.C.andThen(cc.fst[A, B], mon.pure[A])
      override def snd[A, B]: ⨂[A, B] -> F[B] = cc.C.andThen(cc.snd[A, B], mon.pure[B])

      override def diag[A]: A -> F[⨂[A, A]] = cc.C.andThen(cc.diag[A], mon.pure[⨂[A, A]])

      override def braid[A, B]: ⨂[A, B] -> F[⨂[B, A]] = ???

      def idl[A] = ???
      def coidl[A] = ???
      def idr[A] = ???
      def coidr[A] = ???

      def C: Subcat.Aux[λ[(a, b) => a -> F[b]], cc.TC] = ???

      def bifunctor: Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] =
        new Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] {
          override def leftMap [A, B, Z](fn: A -> F[Z]): (A ⨂ B) -> F[Z ⨂ B] = ???
          override def rightMap[A, B, Z](fn: B -> F[Z]): (A ⨂ B) -> F[A ⨂ Z] = ???
          override def bimap[A, X, B, Y](left: A -> F[X], right: B -> F[Y]): (A ⨂ B) -> F[X ⨂ Y] = ???
        }

      def associate[X, Y, Z] = ???
      def diassociate[X, Y, Z] = ???
    }
    ???
  }
}