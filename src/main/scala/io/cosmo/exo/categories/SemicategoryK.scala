package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.*

trait SemicategoryK[->[_,_]]:
  self =>
  def andThen[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> G[a] -> H[a]]): ∀[[a] =>> F[a] -> H[a]]

  final def compose[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> G[a] -> H[a]]): ∀[[a] =>> F[a] -> H[a]] =
    andThen(f, g)

  def lower: Semicategory[->] = new Semicategory[->]:
    def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C =
      self.andThen[[a] =>> A, [a] =>> B, [a] =>> C](∀.of[[a] =>> A -> B](ab), ∀.of[[a] =>> B -> C](bc)).apply

object SemicategoryK extends SemicategoryKInstances:
  def apply[->[_,_]](using ev: SemicategoryK[->]): SemicategoryK[->] = ev
  
  given lowerIso[->[_,_]]: (SemicategoryK[->] <=> Semicategory[->]) = Iso.unsafe(_.lower, _.semicatK)

end SemicategoryK

import SemicategoryKInstancesHelpers.*

private trait SemicategoryKInstances extends SemicategoryKInstances01:
  given distributiveKUpper[->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI](using s: Distributive.Aux[->, T, ⨂, PI, ⨁, SI])
  : DistributiveK.Aux[->, [f[_]] =>> ∀[[a] =>> T[f[a]]], ⨂, [a] =>> PI, ⨁, [a] =>> SI] =
    new DistributiveKUpper[->, T, ⨂, PI, ⨁, SI] { val S = s }
end SemicategoryKInstances

private trait SemicategoryKInstances01 extends SemicategoryKInstances02:
  given groupoidKUpper[->[_,_], T[_]](using s: Groupoid.Aux[->, T]): GroupoidK.Aux[->, [f[_]] =>> ∀[[a] =>> T[f[a]]]] =
    new GroupoidKUpper[->, T] { val S = s }
end SemicategoryKInstances01

private trait SemicategoryKInstances02 extends SemicategoryKInstances03:
  given subcatKUpper[->[_,_], T[_]](using s: Subcategory.Aux[->, T]): SubcategoryK.Aux[->, [f[_]] =>> ∀[[a] =>> T[f[a]]]] =
    new SubcatKUpper[->, T] { val S = s }
end SemicategoryKInstances02

private trait SemicategoryKInstances03:
  given semicatKUpper[->[_,_]](using s: Semicategory[->]): SemicategoryK[->] =
    new SemicatKUpper[->] { val S = s }
end SemicategoryKInstances03

private object SemicategoryKInstancesHelpers:
  trait SemicatKUpper[->[_,_]] extends SemicategoryK[->]:
    protected def S: Semicategory[->]
    def andThen[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> G[a] -> H[a]]): ∀[[a] =>> F[a] -> H[a]] =
      ∀[[a] =>> F[a] -> H[a]](S.andThen(f.apply, g.apply))
  trait SubcatKUpper[->[_,_], T[_]] extends SemicatKUpper[->] with SubcategoryK[->]:
    type TC[f[_]] = ∀[[a] =>> T[f[a]]]
    protected def S: Subcategory.Aux[->, T]
    def id[F[_]: TC]: ∀[[a] =>> F[a] -> F[a]] = ∀[[a] =>> F[a] -> F[a]](S.id(using summon[TC[F]].apply))
  trait DistributiveKUpper[->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI] extends SubcatKUpper[->, T] with DistributiveK[->, ⨂, ⨁]:
    type ProductId[a] = PI
    type SumId[a] = SI
    protected def S: Distributive.Aux[->, T, ⨂, PI, ⨁, SI]
    def cartesian: CartesianK.Aux[->, ⨂, TC, ProductId] = AssociativeK.cartesianKUpper(using S.cartesian)
    def cocartesian: CocartesianK.Aux[->, ⨁, TC, SumId] = AssociativeK.cartesianKUpper(using S.cocartesian)
    def distribute[F[_], G[_], H[_]](using f: TC[F], g: TC[G], h: TC[H])
    : ∀[[a] =>> F[a] ⨂ (G[a] ⨁ H[a]) -> (F[a] ⨂ G[a] ⨁ (F[a] ⨂ H[a]))] =
      ∀[[a] =>> F[a] ⨂ (G[a] ⨁ H[a]) -> (F[a] ⨂ G[a] ⨁ (F[a] ⨂ H[a]))](S.distribute(using f.apply, g.apply, h.apply))
  trait GroupoidKUpper[->[_,_], T[_]] extends SubcatKUpper[->, T] with GroupoidK[->]:
    protected def S: Groupoid.Aux[->, T]
    def flip[F[_], G[_]](f: ∀[[a] =>> F[a] -> G[a]]): ∀[[a] =>> G[a] -> F[a]] = ∀[[a] =>> G[a] -> F[a]](S.flip(f.apply))
end SemicategoryKInstancesHelpers
