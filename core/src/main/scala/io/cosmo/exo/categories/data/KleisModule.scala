package io.cosmo.exo.categories.data

import cats.{Id, Monad}
import io.cosmo.exo.categories.Subcat.Aux
import io.cosmo.exo.categories.{Cartesian, Endobifunctor, HasTerminalObject, Kleis, Opp, Subcat}
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
    term: HasTerminalObject.AuxTerm[->, Term],
    mon: Exomonad[* => *, Id, F],
    bif: Endobifunctor[* => *, ⨂],
    pro: Exobifunctor.Pro[->],
  ): Cartesian[λ[(a,b) => a -> F[b]], ⨂] = {
    new Cartesian[λ[(a,b) => a -> F[b]], ⨂] {
      type TC[a] = cc.TC[a]
      type Id = term.Terminal

      override def &&&[X, Y, Z](f: X -> F[Y], g: X -> F[Z]): X -> F[Y ⨂ Z] = {
        val x: X -> (F[Y] ⨂ F[Z]) = cc.&&&(f, g)

        ???
      }


      override def fst[A, B]: ⨂[A, B] -> F[A] = pro.rightMap(mon.pure[A])(cc.fst[A, B])

      override def snd[A, B]: ⨂[A, B] -> F[B] = pro.rightMap(mon.pure[B])(cc.snd[A, B])

      override def diag[A]: A -> F[⨂[A, A]] = pro.rightMap(mon.pure[⨂[A, A]])(cc.diag[A])

      override def braid[A, B]: ⨂[A, B] -> F[⨂[B, A]] = ???

      def idl[A] = ???
      def coidl[A] = ???
      def idr[A] = ???
      def coidr[A] = ???

      def C: Subcat.Aux[λ[(a, b) => a -> F[b]], cc.TC] = ???

      def bifunctor: Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] =
        new Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] {
          override def L = ???
          override def R = ???
          override def C = ???
          override def leftMap [A, B, Z](fn: A -> F[Z]): (A ⨂ B) -> F[Z ⨂ B] = ???
          override def rightMap[A, B, Z](fn: B -> F[Z]): (A ⨂ B) -> F[A ⨂ Z] = ???
        }

      def associate[X, Y, Z] = ???
      def diassociate[X, Y, Z] = ???
    }
    ???
  }
}