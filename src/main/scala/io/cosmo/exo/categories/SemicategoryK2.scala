package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.*

trait SemicategoryK2[->[_,_]]:
  self =>
  def andThen[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> G[a, b] -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> H[a, b]]
  final def compose[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> G[a, b] -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> H[a, b]] = andThen(f, g)

  def semicat: Semicategory[->] = new Semicategory[->]:
    def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C =
      self.andThen[[a,b] =>> A, [a,b] =>> B, [a,b] =>> C](∀∀[[a, b] =>> A -> B](ab), ∀∀[[a, b] =>> B -> C](bc)).apply

object SemicategoryK2 extends SemicategoryK2Instances:
  def apply[->[_,_]](using ev: SemicategoryK2[->]): SemicategoryK2[->] = ev

  given lowerIso[->[_,_]]: (SemicategoryK2[->] <=> Semicategory[->]) = Iso.unsafe(_.semicat, _.semicatK2)
  
end SemicategoryK2

import SemicategoryK2InstancesHelpers.*

private trait SemicategoryK2Instances extends SemicategoryK2Instances01:
  given distributiveK2Upper[->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI](using s: Distributive.Aux[->, T, ⨂, PI, ⨁, SI])
  : DistributiveK2.Aux[->, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]], ⨂, [a, b] =>> PI, ⨁, [a, b] =>> SI] =
    new DistributiveK2Upper[->, T, ⨂, PI, ⨁, SI] { val S = s }
end SemicategoryK2Instances

private trait SemicategoryK2Instances01 extends SemicategoryK2Instances02:
  given groupoidK2Upper[->[_,_], T[_]](using s: Groupoid.Aux[->, T]): GroupoidK2.Aux[->, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]]] =
    new GroupoidK2Upper[->, T] { val S = s }
end SemicategoryK2Instances01

private trait SemicategoryK2Instances02 extends SemicategoryK2Instances03:
  given subcatK2Upper[->[_,_], T[_]](using s: Subcategory.Aux[->, T]): SubcategoryK2.Aux[->, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]]] =
    new SubcatK2Upper[->, T] { val S = s }
end SemicategoryK2Instances02

private trait SemicategoryK2Instances03:
  given semicatK2Upper[->[_,_]](using s: Semicategory[->]): SemicategoryK2[->] =
    new SemicatK2Upper[->] { val S = s }
end SemicategoryK2Instances03

private object SemicategoryK2InstancesHelpers:
  trait SemicatK2Upper[->[_,_]] extends SemicategoryK2[->]:
    protected def S: Semicategory[->]
    def andThen[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> G[a, b] -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> H[a, b]] =
      ∀∀[[a, b] =>> F[a, b] -> H[a, b]](S.andThen(f.apply, g.apply))
  trait SubcatK2Upper[->[_,_], T[_]] extends SemicatK2Upper[->] with SubcategoryK2[->]:
    type TC[f[_,_]] = ∀∀[[a, b] =>> T[f[a, b]]]
    protected def S: Subcategory.Aux[->, T]
    def id[F[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] -> F[a, b]] = ∀∀[[a, b] =>> F[a, b] -> F[a, b]](S.id(using summon[TC[F]].apply))
  trait DistributiveK2Upper[->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI] extends SubcatK2Upper[->, T] with DistributiveK2[->, ⨂, ⨁]:
    type ProductId[a, b] = PI
    type SumId[a, b] = SI
    protected def S: Distributive.Aux[->, T, ⨂, PI, ⨁, SI]
    def cartesian: CartesianK2.Aux[->, ⨂, TC, ProductId] = ???
    def cocartesian: CocartesianK2.Aux[->, ⨁, TC, SumId] = ???
    def distribute[F[_,_], G[_,_], H[_,_]](using f: TC[F], g: TC[G], h: TC[H])
    : ∀∀[[a, b] =>> F[a, b] ⨂ (G[a, b] ⨁ H[a, b]) -> (F[a, b] ⨂ G[a, b] ⨁ (F[a, b] ⨂ H[a, b]))] =
      ∀∀[[a, b] =>> F[a, b] ⨂ (G[a, b] ⨁ H[a, b]) -> (F[a, b] ⨂ G[a, b] ⨁ (F[a, b] ⨂ H[a, b]))](S.distribute(using f.apply, g.apply, h.apply))
  trait GroupoidK2Upper[->[_,_], T[_]] extends SubcatK2Upper[->, T] with GroupoidK2[->]:
    protected def S: Groupoid.Aux[->, T]
    def flip[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]]): ∀∀[[a, b] =>> G[a, b] -> F[a, b]] = ∀∀[[a, b] =>> G[a, b] -> F[a, b]](S.flip(f.apply))
end SemicategoryK2InstancesHelpers
