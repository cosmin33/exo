package io.cosmo.exo.categories.data

import io.cosmo.exo.categories.functors._
import io.cosmo.exo.categories.{Cartesian, Endobifunctor, Kleis, Subcat, Terminal}
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

  def bifunctor[->[_,_], F[_], ⨂[_,_]](implicit
    cc: Cartesian[->, ⨂],
    lax: LaxSemigroupal.Endo[->, ⨂, F]
  ): Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] =
    new Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] {
      def bimap[A, X, B, Y](left: A -> F[X], right: B -> F[Y]): (A ⨂ B) -> F[X ⨂ Y] =
        cc.C.andThen(cc.grouped(left, right), lax.product[X, Y])
    }

  def category[->[_,_], T[_], F[_]](implicit
    mon: Exomonad[->, T, F],
    cc: Subcat.Aux[->, T],
  ): Subcat.Aux[λ[(a, b) => a -> F[b]], T] = new Subcat[λ[(a, b) => a -> F[b]]] {
    type TC[a] = cc.TC[a]
    def id[A](implicit A: TC[A]): A -> F[A] = mon.pure[A]
    def andThen[A, B, C](ab: A -> F[B], bc: B -> F[C]): A -> F[C] = cc.andThen(ab, mon.bind(bc))
  }

  implicit def kleisCartesian[->[_,_], ⨂[_,_], F[_], T[_], Term](implicit
    c: Cartesian.Aux[->, ⨂, T, Term],
    t: Terminal.Aux[->, T, Term],
    mon: Exomonad[->, T, F],
    lax: LaxSemigroupal.Endo[->, ⨂, F],
    lt: LaxSemigroupal[* => *, ⨂, * => *, (*, *), T]
  ): Cartesian.Aux[λ[(a,b) => a -> F[b]], ⨂, T, Term] =
    new Cartesian[λ[(a,b) => a -> F[b]], ⨂] {
      type TC[a] = T[a]
      type Id = Term
      private implicit val tcTerm: TC[Term] = t.terminalTC
      private implicit def tcProd[A, B](implicit a: TC[A], b: TC[B]): TC[A ⨂ B] = lt.product[A, B]((a, b))
      def C: Subcat.Aux[λ[(a, b) => a -> F[b]], T] = KleisModule.category
      def bifunctor: Endobifunctor[λ[(a, b) => a -> F[b]], ⨂] = KleisModule.bifunctor
      def associate  [X: TC, Y: TC, Z: TC]: X ⨂ Y ⨂ Z -> F[X ⨂ (Y ⨂ Z)] = c.C.andThen(c.associate[X, Y, Z], mon.pure[X ⨂ (Y ⨂ Z)])
      def diassociate[X: TC, Y: TC, Z: TC]: X ⨂ (Y ⨂ Z) -> F[X ⨂ Y ⨂ Z] = c.C.andThen(c.diassociate[X, Y, Z], mon.pure)
      def &&&[X, Y, Z](f: X -> F[Y], g: X -> F[Z]): X -> F[Y ⨂ Z] = c.C.andThen(c.&&&(f, g), lax.product[Y, Z])
      def idl  [A: TC]: Term ⨂ A -> F[A] = c.C.andThen(c.snd[Term, A], mon.pure[A])
      def coidl[A: TC]: A -> F[Term ⨂ A] = c.C.andThen(c.coidl[A], mon.pure[Term ⨂ A])
      def idr  [A: TC]: A ⨂ Term -> F[A] = c.C.andThen(c.fst[A, Term], mon.pure[A])
      def coidr[A: TC]: A -> F[A ⨂ Term] = c.C.andThen(c.coidr[A], mon.pure[A ⨂ Term])
      def fst[A: TC, B: TC]: ⨂[A, B] -> F[A] = c.C.andThen(c.fst[A, B], mon.pure[A])
      def snd[A: TC, B: TC]: ⨂[A, B] -> F[B] = c.C.andThen(c.snd[A, B], mon.pure[B])
      def diag[A: TC]: A -> F[A ⨂ A] = c.C.andThen(c.diag[A], mon.pure[⨂[A, A]])
      def braid[A: TC, B: TC]: (A ⨂ B) -> F[B ⨂ A] = c.C.andThen(c.swap, mon.pure[B ⨂ A])
    }
}