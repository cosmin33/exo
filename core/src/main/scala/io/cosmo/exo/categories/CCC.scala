package io.cosmo.exo.categories

import io.cosmo.exo.categories.functors.Exofunctor
import io.cosmo.exo._

trait Ccc[->[_, _]] extends Subcat[->] {
  type Hom[_, _]

  type ⊙[_, _] // product
  type ProductId
  def cartesian: Cartesian.Aux[->, ⊙, TC, ProductId]

  private type |=>[a,b] = Hom[a,b]
  type Phy[A, B] = ∀[λ[x => (A |=> x) -> (B |=> x)]]
  //Φc : Pre(A, 6)(a, c) ! Pre(A, 6)(b, c)

  def apply[A, B]: ⊙[A |=> B, A] -> B

  def apExperiment1[A, B]: (A |=> B) -> (A |=> B) = curry(apply)
  def apExperiment2[A, B](in: ProductId -> (A |=> B)): A -> B = andThen(cartesian.coidl[A], uncurry(in))
  // apply obtained uncurrying the identity of Hom (but I have to request the typeclass)
  def apExperiment3[A, B](implicit tc: TC[A |=> B]): ⊙[A |=> B, A] -> B = uncurry(id[A |=> B])

  def curry  [A, B, C](f: ⊙[A, B] -> C): A -> (B |=> C)
  def uncurry[A, B, C](f: A -> (B |=> C)): ⊙[A, B] -> C

  /** Adjunction between ⊙[*, B] and B |=> * */
  def isoClosedAdjunction[A, B, C]: (⊙[A, B] -> C) <=> (A -> (B |=> C)) = Iso.unsafe(curry, uncurry)
}

object Ccc {
  type Aux[->[_, _], P[_, _], ->#[_], PI, E[_, _]] = Ccc[->] {
    type Hom[A, B] = E[A, B]
    type ⊙[A, B] = P[A, B]
    type TC[x] = ->#[x]
    type ProductId = PI
  }
  type AuxPH[->[_,_], P[_,_], E[_,_]] = Ccc[->] {type ⊙[A, B] = P[A, B]; type Hom[A, B] = E[A, B]}
  type AuxTC[->[_,_], ->#[_]] = Ccc[->] { type TC[a] = ->#[a] }
  //type Homoiconic[->[_,_]] = InstanceOf[CccClass.Homoiconic[->]]

  trait Proto[->[_, _], P[_, _], ->#[_], PI, E[_, _]] extends Ccc[->] with Subcat.Proto[->, ->#] {
    override type TC[a] = ->#[a]
    type Hom[A, B] = E[A, B]
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