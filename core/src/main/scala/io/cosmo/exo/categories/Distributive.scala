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
      cocartesian.bifunctor.bimap(Dual(cartesian.snd[A, B]), Dual(cartesian.snd[A, C]))
    )

  private type <->[a, b] = Iso[->, a, b]
  def isoDistributive[A, B, C](using a: TC[A], b: TC[B], c: TC[C]): (A ⨂ (B ⨁ C)) <-> ((A ⨂ B) ⨁ (A ⨂ C)) =
    Iso.unsafe(distribute(using a, b, c), codistribute(using a, b, c))(using this)
}
object Distributive {
  type Aux[==>[_, _], =>#[_], P[_, _], PI, S[_, _], SI] = Distributive[==>, P, S] {
    type TC[a] = =>#[a]; type ProductId = PI; type SumId = SI
  }
  type Aux1[==>[_, _], =>#[_], P[_, _], S[_, _]] = Distributive[==>, P, S] { type TC[a] = =>#[a] }

  def apply[->[_, _], ⨂[_,_], ⨁[_,_]](using D: Distributive[->, ⨂, ⨁]): Distributive.Aux[->, D.TC, ⨂, D.ProductId, ⨁, D.SumId] = D

  trait Proto[->[_, _], C[_], P[_, _], PI, S[_, _], SI] extends Distributive[->, P, S] with Subcategory.Proto[->, C] {
    type ProductId = PI
    type SumId = SI
  }

}

