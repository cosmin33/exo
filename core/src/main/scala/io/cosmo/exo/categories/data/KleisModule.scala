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

  def bifunctor[->[_,_], F[_], ⨂[_,_]](implicit
    cc: Cartesian[->, ⨂],
    lax: LaxSemigroupal[->, ⨂, ->, ⨂, F]
  ): Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] =
    new Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] {
      def bimap[A, X, B, Y](left: A -> F[X], right: B -> F[Y]): (A ⨂ B) -> F[X ⨂ Y] =
        cc.C.andThen(cc.grouped(left, right), lax.product[X, Y])
    }

  def category[->[_,_], ⨂[_,_], F[_]](implicit
    mon: Exomonad[->, Id, F],
    cc: Cartesian[->, ⨂],
  ): Subcat.Aux[λ[(a, b) => a -> F[b]], cc.TC] = new Subcat[λ[(a, b) => a -> F[b]]] {
    type TC[a] = cc.TC[a]
    def id[A](implicit A: TC[A]): A -> F[A] = mon.pure[A]
    def andThen[A, B, C](ab: A -> F[B], bc: B -> F[C]): A -> F[C] = cc.C.andThen(ab, mon.bind(bc))
  }

  def kleisCartesian[->[_,_], ⨂[_,_], F[_], Term](implicit
    cc: Cartesian[->, ⨂] { type Id = Term },
    term: Terminal.AuxTerm[->, Term],
    mon: Exomonad[->, Id, F],
    lax: LaxSemigroupal[->, ⨂, ->, ⨂, F]
  ): Cartesian[λ[(a,b) => a -> F[b]], ⨂] =
    new Cartesian[λ[(a,b) => a -> F[b]], ⨂] {
      type TC[a] = cc.TC[a]
      type Id = term.Terminal
      def C: Subcat.Aux[λ[(a, b) => a -> F[b]], cc.TC] = KleisModule.category
      def bifunctor: Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] = KleisModule.bifunctor
      def associate[X, Y, Z] = ???
      def diassociate[X, Y, Z] = ???
      def &&&[X, Y, Z](f: X -> F[Y], g: X -> F[Z]): X -> F[Y ⨂ Z] = cc.C.andThen(cc.&&&(f, g), lax.product[Y, Z])
      def idl  [A: TC]: Term ⨂ A -> F[A] = cc.C.andThen(cc.snd[Term, A], mon.pure[A])
      def coidl[A: TC]: A -> F[Term ⨂ A] = cc.C.andThen(cc.coidl[A], mon.pure[Term ⨂ A])
      def idr  [A: TC]: A ⨂ Term -> F[A] = cc.C.andThen(cc.fst[A, Term], mon.pure[A])
      def coidr[A: TC]: A -> F[A ⨂ Term] = cc.C.andThen(cc.coidr[A], mon.pure[A ⨂ Term])
      def fst[A: TC, B]: ⨂[A, B] -> F[A] = cc.C.andThen(cc.fst[A, B], mon.pure[A])
      def snd[A, B: TC]: ⨂[A, B] -> F[B] = cc.C.andThen(cc.snd[A, B], mon.pure[B])
      def diag[A: TC]: A -> F[A ⨂ A] = cc.C.andThen(cc.diag[A], mon.pure[⨂[A, A]])
      def braid[A, B]: (A ⨂ B) -> F[B ⨂ A] = cc.C.andThen(cc.swap, mon.pure[B ⨂ A])
    }
}