package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.evidence._

import scala.language.experimental.macros

trait Subcat[->[_, _]] extends Semicategory[->] {
  type TC[_]
  def id[A](implicit A: TC[A]): A -> A
}

object Subcat {
  def apply[->[_,_]](implicit c: Subcat[->]): Aux[->, c.TC] = c
  type Aux[->[_,_], T[_]] = Subcat[->] {type TC[a] = T[a]}
  type AuxT[->[_,_]] = Aux[->, Trivial.T1]

  trait Proto[->[_,_], ->#[_]] extends Subcat[->] {type TC[a] = ->#[a]}

  implicit class SubcatOps[->[_,_], T[_]](val s: Subcat.Aux[->, T]) extends AnyVal {
    def dual: Subcat.Aux[Dual[->,*,*], T] = DualModule.dualSubcat[->, T](s)
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
  implicit final class ToSemicategoryOps[->[_, _], B, C](self: B -> C) {
    private def compose[A](f: A -> B)(implicit ev: Semicategory[->]): A -> C = ev.andThen(f, self)
    private def andThen[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = ev.andThen(self, f)
    def <<<<[A](f: A -> B)(implicit ev: Semicategory[->]): A -> C = compose(f)
    def >>>>[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = andThen(f)

    def followedBy[D](f: C -> D)(implicit ev: Semicategory[->]): B -> D = ev.andThen(self, f)

    def flipped(implicit C: Groupoid[->]): C -> B = C.flip(self)

    def dual: Dual[->, C, B] = Dual(self)

    def associateR[X, Y, Z, ⊙[_,_], TC[_]](implicit
      A: Associative.Aux[->, ⊙, TC], ev: C === ⊙[⊙[X, Y], Z], c: Subcat.Aux[->, TC],
      tx: TC[X], ty: TC[Y], tz: TC[Z]
    ): B -> ⊙[X, ⊙[Y, Z]] = A.C.andThen(ev.subst[λ[X => B -> X]](self), A.associate[X, Y, Z])

    def diassociateR[X, Y, Z, ⊙[_,_], TC[_]](implicit
      A: Associative.Aux[->, ⊙, TC], ev: C === ⊙[X, ⊙[Y, Z]], c: Subcat.Aux[->, TC],
      tx: TC[X], ty: TC[Y], tz: TC[Z]
    ): B -> ⊙[⊙[X, Y], Z] = A.C.andThen(ev.subst[λ[X => B -> X]](self), A.diassociate[X, Y, Z])

    def braid[X, Y, ⊙[_,_]] = new BraidOps[X, Y, ⊙]
    class BraidOps[X, Y, ⊙[_,_]] {
      def apply[T[_], BT[_]](implicit
        B: Braided.Aux[->, ⊙, BT], ev: C === ⊙[X, Y], c: Subcat.Aux[->, T], evb: T =~= BT,
        tx: T[X], ty: T[Y]
      ): B -> ⊙[Y, X] = B.C.andThen(ev.subst[λ[α => B -> α]](self), B.braid[X, Y](evb(tx), evb(ty)))
    }

    def curry[P[_, _], X, Y, Z, E[_,_]](f: P[X, Y] -> Z)(implicit
      C: Ccc[->] {type ⊙[a, b] = P[a, b]; type |->[a, b] = E[a, b]}
    ): X -> E[Y, Z] = C.curry(f)

    def uncurry[E[_, _], X, Y, Z, P[_, _]](f: X -> E[Y, Z])(implicit
      C: Ccc[->] {type ⊙[a, b] = P[a, b]; type |->[a, b] = E[a, b]}
    ): P[X, Y] -> Z = C.uncurry(f)

    def split[⊙[_,_], D](fn: D -> C)(implicit
      c: Cocartesian[->, ⊙]
    ): ⊙[B, D] -> C = c.|||(self, fn)

    def split3[⊙[_,_], D, E](f1: D -> C, f2: E -> C)(implicit
      c: Cocartesian[->, ⊙]
    ): ⊙[B, ⊙[D, E]] -> C = c.|||(self, c.|||(f1, f2))

    def merge[⊙[_,_], D](fn: B -> D)(implicit
      c: Cartesian[->, ⊙]
    ): B -> ⊙[C, D] = c.&&&(self, fn)

    def merge3[⊙[_,_], D, E](f1: B -> D, f2: B -> E)(implicit
      c: Cartesian[->, ⊙]
    ): B -> ⊙[C, ⊙[D, E]] = c.&&&(self, c.&&&(f1, f2))

  }
}
