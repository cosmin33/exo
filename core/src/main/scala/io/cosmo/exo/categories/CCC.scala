package io.cosmo.exo.categories

import io.cosmo.exo.{categories, _}


/**
 * From Emily Pi's "The Yoneda Perspective" slides
 * --------------------------------------------------------------------
 * | Types      | Sets          | # of Inhabitants | Categories       |
 * | a          | A             | |A|              | objects of C     |
 * | (a, b)     | A × B         | |A| × |B|        | c × d            |
 * | Either a b | A t B         | |A| + |B|        | c + d            |
 * | a → b      | set functions | |B| |A|          | morphisms in C   |
 * | ()         | {∗}           | 1                | terminal objects |
 * | Void       | ∅             | 0                | initial objects  |
 * --------------------------------------------------------------------
 * Cartesian Closed Category class
 * -------------------------------
 */
trait Ccc[->[_, _]] extends Subcat[->] {
  type Hom[_, _]

  type ⊙[_, _]
  type ProductId
  def cartesian: Cartesian.Aux[->, ⊙, TC, ProductId]

  def apply[A, B]: ⊙[Hom[A, B], A] -> B

  def curry  [A, B, C](f: ⊙[A, B] -> C): A -> Hom[B, C]
  def uncurry[A, B, C](f: A -> Hom[B, C]): ⊙[A, B] -> C

  def isoCurry[A, B, C]: (⊙[A, B] -> C) <=> (A -> Hom[B, C]) = Iso.unsafeT(curry, uncurry)
}

object Ccc {
  type Aux[->[_, _], P[_, _], ->#[_], PI, E[_, _]] = Ccc[->] {
    type Hom[A, B] = E[A, B]
    type ⊙[A, B] = P[A, B]
    type TC[x] = ->#[x]
    type ProductId = PI
  }
  type AuxTC[->[_,_], ->#[_]] = Ccc[->] { type TC[a] = ->#[a] }
  //type Homoiconic[->[_,_]] = InstanceOf[CccClass.Homoiconic[->]]

  trait Proto[->[_, _], P[_, _], ->#[_], PI, E[_, _]] extends Ccc[->] with Subcat.Proto[->, ->#] {
    override type TC[ᵒ] = ->#[ᵒ]
    type Hom[A, B] = E[A, B]
    type ⊙[A, B] = P[A, B]
    type ProductId = PI
  }

}

trait CccImplicits

//trait CccSyntax {
//  implicit final class CccOps[->[_,_], A, B](self: A -> B) {
//
//  }
////  implicit def coCccOps[->[_,_], TC[_], P[_,_], PI, E[_,_]](
////    source: CccAux[λ[(a, b) => b -> a], TC, P, PI, E]
////  ): CoCccOps[->, TC, P, PI, E] =
////    new CoCccOps[->, TC, P, PI, E](source)
////
////  class CoCccOps[->[_,_], TC[_], ⊙[_,_], PI, E[_,_]](c: CccAux[λ[(a, b) => b -> a], TC, ⊙, PI, E]) {
////    object opp {
////      def cocartesian: Cartesian.Aux[λ[(a, b) => b -> a], TC, ⊙, PI] = c.cartesian
////      def coapply[A, B]: B -> ⊙[E[A, B], A] = c.apply
////      def cocurry[X, Y, Z](f: Z -> ⊙[X, Y]): E[Y, Z] -> X = c.curry(f)
////      def councurry[X, Y, Z](f: E[Y, Z] -> X): Z -> ⊙[X, Y] = c.uncurry(f)
////    }
////  }
//}
//
//trait CccInstances {
//
//}