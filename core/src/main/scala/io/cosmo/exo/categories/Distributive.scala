package io.cosmo.exo.categories

import io.cosmo.exo._

trait Distributive[->[_, _], ⨂[_, _], ⨁[_, _]] extends Subcat[->] {
  type ProductId
  type SumId
  def cartesian: Cartesian.Aux[->, ⨂, TC, ProductId]
  def cocartesian: Cocartesian.Aux[->, ⨁, TC, SumId]

  def distribute[A: TC, B: TC, C: TC]: ⨂[A, ⨁[B, C]] -> ⨁[⨂[A, B], ⨂[A, C]]

  def codistribute[A: TC, B: TC, C: TC]: ⨁[⨂[A, B], ⨂[A, C]] -> ⨂[A, ⨁[B, C]] =
    cartesian.&&&(
      cocartesian.|||(cartesian.fst[A, B], cartesian.fst[A, C]),
      cocartesian.bifunctor.bimap(Dual(cartesian.snd[A, B]), Dual(cartesian.snd[A, C])).toFn
    )

  private type <->[a, b] = Iso[->, a, b]
  def isoDistributive[A, B, C](implicit a: TC[A], b: TC[B], c: TC[C]): ⨂[A, ⨁[B, C]] <-> ⨁[⨂[A, B], ⨂[A, C]] =
    Iso.unsafe(distribute(a, b, c), codistribute(a, b, c))(this)
}
object Distributive {
  type Aux[==>[_, _], =>#[_], P[_, _], PI, S[_, _], SI] = Distributive[==>, P, S] {
    type TC[a] = =>#[a]; type ProductId = PI; type SumId = SI
  }
  type Aux1[==>[_, _], =>#[_], P[_, _], S[_, _]] = Distributive[==>, P, S] { type TC[a] = =>#[a] }

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

  trait Proto[->[_, _], C[_], P[_, _], PI, S[_, _], SI] extends Distributive[->, P, S] with Subcat.Proto[->, C] {
    type ProductId = PI
    type SumId = SI
  }

  def unsafe[->[_,_], ⨂[_,_], ⨁[_,_], ->#[_], PI, SI](
    ft: ∀∀∀[λ[(a,b,c) => ⨂[a, ⨁[b, c]] -> ⨁[⨂[a, b], ⨂[a, c]]]]
  )(implicit
    CP: Cartesian.Aux[->, ⨂, ->#, PI],
    CS: Cartesian.Aux[Dual[->,*,*], ⨁, ->#, SI],
  ): Distributive.Aux[->, ->#, ⨂, PI, ⨁, SI] =
    new Distributive.Proto[->, ->#, ⨂, PI, ⨁, SI] {
      def cartesian = CP
      def cocartesian = CS
      def id[A](implicit A: ->#[A]) = CP.C.id[A]
      def andThen[A, B, C](ab: A -> B, bc: B -> C) = CP.C.andThen(ab, bc)
      def distribute[A: TC, B: TC, C: TC] = ft[A, B, C]
    }

  def apply[->[_, _], P[_,_], S[_,_]](implicit
    D: Distributive[->, P, S]
  ): Distributive.Aux[->, D.TC, P, D.ProductId, S, D.SumId] = D

}

