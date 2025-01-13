package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.*

trait SemicategoryH[->[_,_]]:
  self =>
  def andThen[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]], g: ∀~[[a[_]] =>> G[a] -> H[a]]): ∀~[[a[_]] =>> F[a] -> H[a]]
  final def compose[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]], g: ∀~[[a[_]] =>> G[a] -> H[a]]): ∀~[[a[_]] =>> F[a] -> H[a]] = andThen(f, g)
  
  def semicat: Semicategory[->] = new Semicategory[->]:
    def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C =
      self.andThen[[a[_]] =>> A, [a[_]] =>> B, [a[_]] =>> C](∀~[[a[_]] =>> A -> B](ab), ∀~[[a[_]] =>> B -> C](bc)).apply
      
object SemicategoryH extends SemicategoryHInstances:
  def apply[->[_,_]](using ev: SemicategoryH[->]): SemicategoryH[->] = ev
  
  given lowerIso[->[_,_]]: (SemicategoryH[->] <=> Semicategory[->]) = Iso.unsafe(_.semicat, _.semicatH)
  
end SemicategoryH

import SemicategoryHInstancesHelpers.*

private trait SemicategoryHInstances extends SemicategoryHInstances01:
  given distributiveHUpper[->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI](using s: Distributive.Aux[->, T, ⨂, PI, ⨁, SI])
  : DistributiveH.Aux[->, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]], ⨂, [a[_]] =>> PI, ⨁, [a[_]] =>> SI] =
    new DistributiveHUpper[->, T, ⨂, PI, ⨁, SI] { val S = s }
end SemicategoryHInstances

private trait SemicategoryHInstances01 extends SemicategoryHInstances02:
  given groupoidHUpper[->[_,_], T[_]](using s: Groupoid.Aux[->, T]): GroupoidH.Aux[->, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]]] =
    new GroupoidHUpper[->, T] { val S = s }
end SemicategoryHInstances01

private trait SemicategoryHInstances02 extends SemicategoryHInstances03:
  given subcatHUpper[->[_,_], T[_]](using s: Subcategory.Aux[->, T]): SubcategoryH.Aux[->, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]]] =
    new SubcatHUpper[->, T] { val S = s }
end SemicategoryHInstances02

private trait SemicategoryHInstances03:
  given semicatHUpper[->[_,_]](using s: Semicategory[->]): SemicategoryH[->] =
    new SemicatHUpper[->] { val S = s }
end SemicategoryHInstances03

private object SemicategoryHInstancesHelpers:
  trait SemicatHUpper[->[_,_]] extends SemicategoryH[->]:
    protected def S: Semicategory[->]
    def andThen[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]], g: ∀~[[a[_]] =>> G[a] -> H[a]]): ∀~[[a[_]] =>> F[a] -> H[a]] =
      ∀~[[a[_]] =>> F[a] -> H[a]](S.andThen(f.apply, g.apply))
  trait SubcatHUpper[->[_,_], T[_]] extends SemicatHUpper[->] with SubcategoryH[->]:
    type TC[f[_[_]]] = ∀~[[a[_]] =>> T[f[a]]]
    protected def S: Subcategory.Aux[->, T]
    def id[F[_[_]]: TC]: ∀~[[a[_]] =>> F[a] -> F[a]] = ∀~[[a[_]] =>> F[a] -> F[a]](S.id(using summon[TC[F]].apply))
  trait DistributiveHUpper[->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI] extends SubcatHUpper[->, T] with DistributiveH[->, ⨂, ⨁]:
    type ProductId[a[_]] = PI
    type SumId[a[_]] = SI
    protected def S: Distributive.Aux[->, T, ⨂, PI, ⨁, SI]
    def cartesian: CartesianH.Aux[->, ⨂, TC, ProductId] = AssociativeH.cartesianHUpper(using S.cartesian)
    def cocartesian: CocartesianH.Aux[->, ⨁, TC, SumId] = AssociativeH.cartesianHUpper(using S.cocartesian)
    def distribute[F[_[_]], G[_[_]], H[_[_]]](using f: TC[F], g: TC[G], h: TC[H])
    : ∀~[[a[_]] =>> F[a] ⨂ (G[a] ⨁ H[a]) -> (F[a] ⨂ G[a] ⨁ (F[a] ⨂ H[a]))] =
      ∀~[[a[_]] =>> F[a] ⨂ (G[a] ⨁ H[a]) -> (F[a] ⨂ G[a] ⨁ (F[a] ⨂ H[a]))](S.distribute(using f.apply, g.apply, h.apply))
  trait GroupoidHUpper[->[_,_], T[_]] extends SubcatHUpper[->, T] with GroupoidH[->]:
    protected def S: Groupoid.Aux[->, T]
    def flip[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]]): ∀~[[a[_]] =>> G[a] -> F[a]] = ∀~[[a[_]] =>> G[a] -> F[a]](S.flip(f.apply))
end SemicategoryHInstancesHelpers
