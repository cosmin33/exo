package io.cosmo.exo.categories

import cats.implicits._
import io.cosmo.exo._

trait Distributive[->[_, _]] extends Subcat[->] {
  type ProductId
  type ⨂[_, _]
  type SumId
  type ⨁[_, _]
  def cartesian: Cartesian.Aux[->, ⨂, TC, ProductId]
  def cocartesian: Cartesian.Aux[Opp[->]#l, ⨁, TC, SumId]
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

  def unsafe[->[_,_], ->#[_], P[_,_], S[_,_], PI, SI](
    ft: ∀∀∀[λ[(a,b,c) => P[a, S[b, c]] -> S[P[a, b], P[a, c]]]]
  )(implicit
    CP: Cartesian.Aux[->, P, ->#, PI],
    CS: Cartesian.Aux[Opp[->]#l, S, ->#, SI],
  ): Distributive.Aux[->, ->#, P, PI, S, SI] =
      new Distributive.Proto[->, ->#, P, PI, S, SI] {
        def cartesian = CP
        def cocartesian = CS
        def id[A](implicit A: ->#[A]) = CP.C.id[A]
        def andThen[A, B, C](ab: A -> B, bc: B -> C) = CP.C.andThen(ab, bc)
        def distribute[A, B, C] = ft[A, B, C]
      }


  def distFunc1TupleDisj(implicit
    C1: Cartesian.Aux[* => *, Tuple2, Trivial.T1, Unit],
    C2: Cartesian.Aux[Opp[* => *]#l, \/, Trivial.T1, Void]
  ): Distributive.Aux[* => *, Trivial.T1, Tuple2, Unit, \/, Void] =
    unsafe(∀∀∀.of[λ[(a,b,c) => ((a, b \/ c)) => ((a, b) \/ (a, c))]].from(
      {case (a, e) => e.fold((a, _).left, (a, _).right)})
    )(C1, C2)

  def apply[->[_, _]](implicit
    D: Distributive[->]
  ): Distributive.Aux[->, D.TC, D.⨂, D.ProductId, D.⨁, D.SumId] = D

}

trait DistributiveImplicits {

}
