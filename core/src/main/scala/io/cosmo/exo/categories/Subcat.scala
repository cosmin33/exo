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

  implicit class SubcatOps[->[_,_]](val s: Subcat[->]) extends AnyVal {
    def opp: Subcat.Aux[Dual[->,*,*], s.TC] = DualModule.dualSubcat[->, s.TC](s)
  }

}

trait SubcatHasId[->[_,_], A] {
  type TC[_]
  val s: Subcat.Aux[->, TC]
  val t: TC[A]
  def id: A -> A = s.id(t)
}
object SubcatHasId {
  def apply[->[_,_], A](implicit sub: SubcatHasId[->, A]): SubcatHasId[->, A] = sub

  implicit def from[->[_,_], A, T[_]](implicit sub: Subcat.Aux[->, T], tc: T[A]): SubcatHasId[->, A] =
    new SubcatHasId[->, A] { type TC[a] = T[a]; val s = sub; val t = tc }
}


trait SubcategorySyntax {
  implicit final class ToCategoryOps[->[_, _], B, C](self: B -> C) {
    def compose[A](f: A -> B)(implicit ev: Semicategory[->]): A -> C = macro ops.Ops.ia_1
    def andThen[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = macro ops.Ops.ia_1
    type compose
    type andThen
    def <<<<[A](f: A -> B)(implicit ev: Semicategory[->]): A -> C = macro ops.Ops.nia_1[compose]
    def >>>>[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = macro ops.Ops.nia_1[andThen]

    def followedBy[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = ev.andThen(self, f)

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

    def curry[P[_, _], X, Y, Z, E[_,_]](f: P[X, Y] -> Z)(implicit
      C: Ccc[->] {type ⊙[a, b] = P[a, b]; type |->[a, b] = E[a, b]}
    ): X -> E[Y, Z] = C.curry(f)

    def uncurry[X, Y, Z, P[_, _], E[_, _]](f: X -> E[Y, Z])(implicit
      C: Ccc[->] {type ⊙[a, b] = P[a, b]; type |->[a, b] = E[a, b]}
    ): P[X, Y] -> Z = C.uncurry(f)
  }
}
