package io.cosmo.exo.categories

import cats.implicits._
import io.cosmo.exo._

trait Distributive[->[_, _]] extends Subcat[->] {
  type ProductId
  type ⨂[_, _]
  type SumId
  type ⨁[_, _]
  def cartesian: Cartesian.Aux[->, ⨂, TC, ProductId]
  def cocartesian: Cartesian.Aux[Dual[->,*,*], ⨁, TC, SumId]

  /** (A, (B \/ C) => (A, B) \/ (A, C) */
  def distribute[A, B, C]: ⨂[A, ⨁[B, C]] -> ⨁[⨂[A, B], ⨂[A, C]]
}
object Distributive {
  type Aux[==>[_, _], =>#[_], P[_, _], PI, S[_, _], SI] = Distributive[==>] {
    type TC[a] = =>#[a]
    type ProductId = PI; type ⨂[A, B] = P[A, B]
    type SumId = SI;     type ⨁[A, B] = S[A, B]
  }
  type AuxTC[==>[_,_], =>#[_]] = Distributive[==>] {type TC[a] = =>#[a]}


  case class SingleOf[T, U <: {type TC[_]; type ProductId; type ⨂[_,_]; type SumId; type ⨁[_,_]}](
    widen: T {
      type TC[a] = U#TC[a]
      type ProductId = U#ProductId
      type ⨂[a,b] = U# ⨂[a,b]
      type SumId = U#SumId
      type ⨁[a,b] = U# ⨁[a,b]
    }
  )
  object SingleOf {
    implicit def mkSingleOf[T <: {type TC[_]; type ProductId; type ⨂[_,_]; type SumId; type ⨁[_,_]}](
      implicit t: T
    ): SingleOf[T, t.type] = SingleOf(t)
  }

  trait Proto[->[_, _], C[_], P[_, _], PI, S[_, _], SI] extends Distributive[->] with Subcat.Proto[->, C]{
    type ProductId = PI; type ⨂[A, B] = P[A, B]
    type SumId = SI;     type ⨁[A, B] = S[A, B]
  }

  def unsafe[->[_,_], ⨂[_,_], ⨁[_,_], ->#[_], PI, SI](
    ft: ∀∀∀[λ[(a,b,c) => ⨂[a, ⨁[b, c]] -> ⨁[⨂[a, b], ⨂[a, c]]]]
  )(implicit
    cat: Subcat.Aux[->, ->#],
    CP: Cartesian.Aux[->, ⨂, ->#, PI],
    CS: Cartesian.Aux[Dual[->,*,*], ⨁, ->#, SI],
  ): Distributive.Aux[->, ->#, ⨂, PI, ⨁, SI] =
    new Distributive.Proto[->, ->#, ⨂, PI, ⨁, SI] {
      def cartesian = CP
      def cocartesian = CS
      def id[A](implicit A: ->#[A]) = cat.id[A]
      def andThen[A, B, C](ab: A -> B, bc: B -> C) = cat.andThen(ab, bc)
      def distribute[A, B, C] = ft[A, B, C]
    }

  def apply[->[_, _]](implicit
    D: Distributive[->]
  ): Distributive.Aux[->, D.TC, D.⨂, D.ProductId, D.⨁, D.SumId] = D

}

