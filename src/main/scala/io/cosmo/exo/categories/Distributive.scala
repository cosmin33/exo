package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*

trait Distributive[->[_,_], ⨂[_,_], ⨁[_,_]] extends Subcat[->]:
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

object Distributive:
  type Aux[==>[_,_], =>#[_], P[_,_], PI, S[_,_], SI] = 
    Distributive[==>, P, S] { type TC[a] = =>#[a]; type ProductId = PI; type SumId = SI }
  type Aux1[==>[_,_], =>#[_], P[_,_], S[_,_]] = Distributive[==>, P, S] { type TC[a] = =>#[a] }
  def apply[->[_,_], ⨂[_,_], ⨁[_,_]](using D: Distributive[->, ⨂, ⨁]): Distributive.Aux[->, D.TC, ⨂, D.ProductId, ⨁, D.SumId] = D

  trait Proto[->[_,_], C[_], P[_,_], PI, S[_,_], SI] extends Distributive[->, P, S] with Subcategory.Proto[->, C]:
    type ProductId = PI
    type SumId = SI

end Distributive

trait DistributiveK[->[_,_], ⨂[_,_], ⨁[_,_]] extends SubcatK[->]:
  type ProductId[_]
  type SumId[_]
  def cartesian: CartesianK.Aux[->, ⨂, TC, ProductId]
  def cocartesian: CocartesianK.Aux[->, ⨁, TC, SumId]

  def distribute[F[_]: TC, G[_]: TC, H[_]: TC]: ∀[[a] =>> ⨂[F[a], ⨁[G[a], H[a]]] -> ⨁[⨂[F[a], G[a]], ⨂[F[a], H[a]]]]

  def codistribute[F[_]: TC, G[_]: TC, H[_]: TC]: ∀[[a] =>> ⨁[⨂[F[a], G[a]], ⨂[F[a], H[a]]] -> ⨂[F[a], ⨁[G[a], H[a]]]] =
    cartesian.&&&[[a] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a]), F, [a] =>> G[a] ⨁ H[a]](
      cocartesian.|||[[a] =>> F[a] ⨂ G[a], [a] =>> F[a] ⨂ H[a], F](cartesian.fst[F, G], cartesian.fst[F, H]),
      ∀[[a] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a]) -> G[a] ⨁ H[a]](
        cocartesian.bifunctor.bimap(
          ∀[[x] =>> Dual[->, G[x], F[x] ⨂ G[x]]](Dual(cartesian.snd[F, G].apply)).apply,
          ∀[[x] =>> Dual[->, H[x], F[x] ⨂ H[x]]](Dual(cartesian.snd[F, H].apply)).apply
        )
      )
    )

  private type <->[a[_], b[_]] = IsoK[->, a, b]
  def isoDistributive[F[_]: TC, G[_]: TC, H[_]: TC]: ([a] =>> F[a] ⨂ (G[a] ⨁ H[a])) <-> ([a] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a])) =
    IsoK.unsafe[->, [a] =>> F[a] ⨂ (G[a] ⨁ H[a]), [a] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a])](distribute[F, G, H], codistribute[F, G, H])(using this.lower)

object DistributiveK:
  type Aux[->[_,_], C[_[_]], ⨂[_,_], PI[_], ⨁[_,_], SI[_]] =
    DistributiveK[->, ⨂, ⨁] { type TC[a[_]] = C[a]; type ProductId[a] = PI[a]; type SumId[a] = SI[a] }
  type AuxT[->[_,_], C[_[_]], ⨂[_,_], ⨁[_,_]] = DistributiveK[->, ⨂, ⨁] { type TC[a[_]] = C[a] }
  def apply[->[_,_], ⨂[_,_], ⨁[_,_]](using D: DistributiveK[->, ⨂, ⨁]): DistributiveK.Aux[->, D.TC, ⨂, D.ProductId, ⨁, D.SumId] = D

  trait Proto[->[_,_], C[_[_]], ⨂[_,_], PI[_], ⨁[_,_], SI[_]] extends DistributiveK[->, ⨂, ⨁] with SubcategoryK.Proto[->, C]:
    type ProductId[a] = PI[a]
    type SumId[a] = SI[a]

end DistributiveK

trait DistributiveK2[->[_,_], ⨂[_,_], ⨁[_,_]] extends SubcatK2[->]:
  type ProductId[_,_]
  type SumId[_,_]
  def cartesian: CartesianK2.Aux[->, ⨂, TC, ProductId]
  def cocartesian: CocartesianK2.Aux[->, ⨁, TC, SumId]

  def distribute[F[_,_]: TC, G[_,_]: TC, H[_,_]: TC]: ∀∀[[a, b] =>> ⨂[F[a, b], ⨁[G[a, b], H[a, b]]] -> ⨁[⨂[F[a, b], G[a, b]], ⨂[F[a, b], H[a, b]]]]

  def codistribute[F[_,_]: TC, G[_,_]: TC, H[_,_]: TC]: ∀∀[[a, b] =>> ⨁[⨂[F[a, b], G[a, b]], ⨂[F[a, b], H[a, b]]] -> ⨂[F[a, b], ⨁[G[a, b], H[a, b]]]] =
    cartesian.&&&[[a, b] =>> (F[a, b] ⨂ G[a, b]) ⨁ (F[a, b] ⨂ H[a, b]), F, [a, b] =>> G[a, b] ⨁ H[a, b]](
      cocartesian.|||[[a, b] =>> F[a, b] ⨂ G[a, b], [a, b] =>> F[a, b] ⨂ H[a, b], F](cartesian.fst[F, G], cartesian.fst[F, H]),
      ∀∀[[a, b] =>> (F[a, b] ⨂ G[a, b]) ⨁ (F[a, b] ⨂ H[a, b]) -> G[a, b] ⨁ H[a, b]](
        cocartesian.bifunctor.bimap(
          ∀∀[[x, y] =>> Dual[->, G[x, y], F[x, y] ⨂ G[x, y]]](Dual(cartesian.snd[F, G].apply)).apply,
          ∀∀[[x, y] =>> Dual[->, H[x, y], F[x, y] ⨂ H[x, y]]](Dual(cartesian.snd[F, H].apply)).apply
        )
      )
    )

  private type <->[a[_,_], b[_,_]] = IsoK2[->, a, b]
  def isoDistributive[F[_,_]: TC, G[_,_]: TC, H[_,_]: TC]: ([a, b] =>> F[a, b] ⨂ (G[a, b] ⨁ H[a, b])) <-> ([a, b] =>> (F[a, b] ⨂ G[a, b]) ⨁ (F[a, b] ⨂ H[a, b])) =
    IsoK2.unsafe[->, [a, b] =>> F[a, b] ⨂ (G[a, b] ⨁ H[a, b]), [a, b] =>> (F[a, b] ⨂ G[a, b]) ⨁ (F[a, b] ⨂ H[a, b])](distribute[F, G, H], codistribute[F, G, H])(using this.lower)

object DistributiveK2:
  type Aux[->[_,_], C[_[_,_]], ⨂[_,_], PI[_,_], ⨁[_,_], SI[_,_]] =
    DistributiveK2[->, ⨂, ⨁] { type TC[a[_,_]] = C[a]; type ProductId[a, b] = PI[a, b]; type SumId[a, b] = SI[a, b] }
  type AuxT[->[_,_], C[_[_,_]], ⨂[_,_], ⨁[_,_]] = DistributiveK2[->, ⨂, ⨁] { type TC[a[_,_]] = C[a] }
  def apply[->[_,_], ⨂[_,_], ⨁[_,_]](using D: DistributiveK2[->, ⨂, ⨁]): DistributiveK2.Aux[->, D.TC, ⨂, D.ProductId, ⨁, D.SumId] = D

  trait Proto[->[_,_], C[_[_,_]], ⨂[_,_], PI[_,_], ⨁[_,_], SI[_,_]] extends DistributiveK2[->, ⨂, ⨁] with SubcategoryK2.Proto[->, C]:
    type ProductId[a, b] = PI[a, b]
    type SumId[a, b] = SI[a, b]

end DistributiveK2

trait DistributiveH[->[_,_], ⨂[_,_], ⨁[_,_]] extends SubcatH[->]:
  type ProductId[_[_]]
  type SumId[_[_]]
  def cartesian: CartesianH.Aux[->, ⨂, TC, ProductId]
  def cocartesian: CocartesianH.Aux[->, ⨁, TC, SumId]

  def distribute[F[_[_]]: TC, G[_[_]]: TC, H[_[_]]: TC]: ∀~[[a[_]] =>> ⨂[F[a], ⨁[G[a], H[a]]] -> ⨁[⨂[F[a], G[a]], ⨂[F[a], H[a]]]]

  def codistribute[F[_[_]]: TC, G[_[_]]: TC, H[_[_]]: TC]: ∀~[[a[_]] =>> ⨁[⨂[F[a], G[a]], ⨂[F[a], H[a]]] -> ⨂[F[a], ⨁[G[a], H[a]]]] =
    cartesian.&&&[[a[_]] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a]), F, [a[_]] =>> G[a] ⨁ H[a]](
      cocartesian.|||[[a[_]] =>> F[a] ⨂ G[a], [a[_]] =>> F[a] ⨂ H[a], F](cartesian.fst[F, G], cartesian.fst[F, H]),
      ∀~[[a[_]] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a]) -> G[a] ⨁ H[a]](
        cocartesian.bifunctor.bimap(
          ∀~[[x[_]] =>> Dual[->, G[x], F[x] ⨂ G[x]]](Dual(cartesian.snd[F, G].apply)).apply,
          ∀~[[x[_]] =>> Dual[->, H[x], F[x] ⨂ H[x]]](Dual(cartesian.snd[F, H].apply)).apply
        )
      )
    )

  private type <->[a[_[_]], b[_[_]]] = IsoH[->, a, b]
  def isoDistributive[F[_[_]]: TC, G[_[_]]: TC, H[_[_]]: TC]: ([a[_]] =>> F[a] ⨂ (G[a] ⨁ H[a])) <-> ([a[_]] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a])) =
    IsoH.unsafe[->, [a[_]] =>> F[a] ⨂ (G[a] ⨁ H[a]), [a[_]] =>> (F[a] ⨂ G[a]) ⨁ (F[a] ⨂ H[a])](distribute[F, G, H], codistribute[F, G, H])(using this.lower)

object DistributiveH:
  type Aux[->[_,_], C[_[_[_]]], ⨂[_,_], PI[_[_]], ⨁[_,_], SI[_[_]]] =
    DistributiveH[->, ⨂, ⨁] { type TC[a[_[_]]] = C[a]; type ProductId[a[_]] = PI[a]; type SumId[a[_]] = SI[a] }
  type AuxT[->[_,_], C[_[_[_]]], ⨂[_,_], ⨁[_,_]] = DistributiveH[->, ⨂, ⨁] { type TC[a[_[_]]] = C[a] }
  def apply[->[_,_], ⨂[_,_], ⨁[_,_]](using D: DistributiveH[->, ⨂, ⨁]): DistributiveH.Aux[->, D.TC, ⨂, D.ProductId, ⨁, D.SumId] = D

  trait Proto[->[_,_], C[_[_[_]]], ⨂[_,_], PI[_[_]], ⨁[_,_], SI[_[_]]] extends DistributiveH[->, ⨂, ⨁] with SubcategoryH.Proto[->, C]:
    type ProductId[a[_]] = PI[a]
    type SumId[a[_]] = SI[a]

end DistributiveH
