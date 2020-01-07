package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.evidence._

import scala.language.experimental.macros

trait Subcat[->[_, _]] extends Semicategory[->] {
  type TC[ᵒ]
  def id[A](implicit A: TC[A]): A -> A
}

object Subcat {
  def apply[->[_,_]](implicit c: Subcat[->]): Aux[->, c.TC] = c
  type Aux[->[_,_], T[_]] = Subcat[->] {type TC[a] = T[a]}
  type AuxT[->[_,_]] = Aux[->, Trivial.T1]

  trait Proto[->[_,_], ->#[_]] extends Subcat[->] {type TC[a] = ->#[a]}

  def oppCategory[->[_,_], C[_]](src: Subcat.Aux[->, C]): Subcat.Aux[Opp[->]#l, C] =
    new SemicategoryHelpers.OppSubcategory[->, C] { val op = src }

  implicit class SubcatOps[->[_,_]](val s: Subcat[->]) extends AnyVal {
    def opp: Subcat.Aux[Dual[->,*,*], s.TC] = DualModule.category[->, s.TC](s)
  }

}

trait SubcategorySyntax {
  implicit final class ToCategoryOps[->[_, _], B, C](self: B -> C) {
    //def compose[A](f: A -> B)(implicit ev: Semicategory[->]): A -> C = macro ops.Ops.ia_1
    //def andThen[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = macro ops.Ops.ia_1
    //type compose
    //type andThen
    //def <<<[A](f: A -> B)(implicit ev: Semicategory[->]): A -> C = macro ops.Ops.nia_1[compose]
    //def >>>[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = macro ops.Ops.nia_1[andThen]

    def followedBy[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = macro ops.Ops.ia_1
    type followedBy
    def >>>>[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = macro ops.Ops.nia_1[followedBy]

    def flipped(implicit C: Groupoid[->]): C -> B = C.flip(self)

    def associateR[X, Y, Z, F[_, _]](implicit
      A: Associative[->, F], ev: C === F[F[X, Y], Z]
    ): B -> F[X, F[Y, Z]] = A.C.andThen(ev.subst[λ[X => B -> X]](self), A.associate[X, Y, Z])

    def diassociateR[X, Y, Z, F[_, _]](implicit
      A: Associative[->, F], ev: C === F[X, F[Y, Z]]
    ): B -> F[F[X, Y], Z] = A.C.andThen(ev.subst[λ[X => B -> X]](self), A.diassociate[X, Y, Z])

    def braidR[X, Y, ⊙[_, _]](implicit
      B: Braided[->, ⊙], ev: C === ⊙[X, Y]
    ): B -> ⊙[Y, X] = B.C.andThen(ev.subst[λ[X => B -> X]](self), B.braid[X, Y])

    def curry[X, Y, Z, C0[_], P[_, _], PI, E[_, _]](f: P[X, Y] -> Z)(implicit
      C: Ccc.Aux[->, P, C0, PI, E]
    ): X -> E[Y, Z] = C.curry(f)

    def uncurry[X, Y, Z, C0[_], P[_, _], PI, E[_, _]](f: X -> E[Y, Z])(implicit
      C: Ccc.Aux[->, P, C0, PI, E]
    ): P[X, Y] -> Z = C.uncurry(f)
  }
}
