package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.categories.functors._

trait Ccc[->[_, _]] extends Subcat[->] {
  type |->[_, _] // Hom functor

  type ⊙[_, _] // product
  type ProductId
  def cartesian: Cartesian.Aux[->, ⊙, TC, ProductId]

  def apply[A, B]: ⊙[A |-> B, A] -> B

//  private def apExperiment1[A, B]: (A |-> B) -> (A |-> B) = uncurry(apply)
//  private def apExperiment2[A, B](in: ProductId -> (A |-> B)): A -> B = andThen(cartesian.coidl[A], curry(in))
//  // apply obtained uncurrying the identity of Hom (but I have to ask for the typeclass)
//  private def curryId  [A, B](implicit tc: TC[A |-> B]): ⊙[A |-> B, A] -> B = curry(id[A |-> B])
//  private def uncurryId[A, B](implicit tc: TC[⊙[A, B]]): A -> (B |-> (A ⊙ B)) = uncurry(id[⊙[A, B]])

  def curry  [A, B, C](f: A -> (B |-> C)): ⊙[A, B] -> C
  def uncurry[A, B, C](f: ⊙[A, B] -> C): A -> (B |-> C)

  /** Adjunction between ⊙[*, B] and B |-> * */
  def isoClosedAdjunction[A, B, C]: (⊙[A, B] -> C) <=> (A -> (B |-> C)) = Iso.unsafe(uncurry, curry)
}

object Ccc {
  type Aux[->[_, _], ->#[_], P[_, _], PI, E[_, _]] = Ccc[->] {
    type |->[A, B] = E[A, B]
    type ⊙[A, B] = P[A, B]
    type TC[x] = ->#[x]
    type ProductId = PI
  }
  type AuxPH[->[_,_], P[_,_], E[_,_]] = Ccc[->] {type ⊙[A, B] = P[A, B]; type Hom[A, B] = E[A, B]}
  type AuxTC[->[_,_], ->#[_]] = Ccc[->] { type TC[a] = ->#[a] }
  //type Homoiconic[->[_,_]] = InstanceOf[CccClass.Homoiconic[->]]

  case class SingleOf[T, U <: {type TC[_]; type |->[_,_]; type ⊙[_, _]; type ProductId}](
    widen: T {type TC[_]; type |->[_,_]; type ⊙[_, _]; type ProductId}
  )
  object SingleOf {
    implicit def mkSingleOf[T <: {type TC[_]; type |->[_,_]; type ⊙[_, _]; type ProductId}](
      implicit t: T
    ): SingleOf[T, t.type] = SingleOf(t)
  }

  trait Proto[->[_, _], P[_, _], ->#[_], PI, E[_, _]] extends Ccc[->] with Subcat.Proto[->, ->#] {
    override type TC[a] = ->#[a]
    type |->[A, B] = E[A, B]
    type ⊙[A, B] = P[A, B]
    type ProductId = PI
  }

}

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