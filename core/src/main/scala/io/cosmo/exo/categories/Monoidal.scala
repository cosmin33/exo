package io.cosmo.exo.categories

import io.cosmo.exo.categories.data.ProdCat
import io.cosmo.exo.categories.data.ProdCat.Dicat
import io.cosmo.exo.categories.functors.Exo
import io.cosmo.exo.{categories, _}

trait Monoidal[->[_, _], ⊙[_, _]] extends Associative[->, ⊙] {
  type Id

  def idl  [A]: ⊙[Id, A] -> A
  def coidl[A]: A -> ⊙[Id, A]

  def idr  [A]: ⊙[A, Id] -> A
  def coidr[A]: A -> ⊙[A, Id]

  private type <->[a, b] = Iso[->, a, b]
  def isoIdL[A]: ⊙[Id, A] <-> A = Iso.unsafe(idl[A], coidl[A])(C)
  def isoIdR[A]: ⊙[A, Id] <-> A = Iso.unsafe(idr[A], coidr[A])(C)
}

//trait ClosedProunit[->[_,_], P[_,_]] extends Associative[->, P] {
//  //type U[x] = x ->
//}
//trait ClosedUnital[->[_,_], P[_,_]] extends ClosedProunit[->, P] {
//  type MUnit
//  type Hom[_,_]
//  private type ==>[a,b] = Hom[a,b]
//  //def HomF: Exo[Dicat[->,*,*], ->, ]
//}

object Monoidal {
  type Aux  [->[_, _], ⊙[_, _], TC0[_], I] = Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }
  type AuxI [->[_, _], ⊙[_, _], I]         = Monoidal[->, ⊙] { type Id = I }
  type AuxTC[->[_, _], ⊙[_, _], TC0[_]]    = Monoidal[->, ⊙] { type TC[a] = TC0[a] }

  type AuxT [->[_, _], ⊙[_, _]] = AuxTC[->, ⊙, Trivial.T1]

  trait Proto[->[_, _], ⊙[_, _], TC0[_], I] extends Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }

}

trait HMonoidal[->[_,_], HList, :::[_, _] <: HList, Nil <: HList] {
  def idn [H]: (H ::: Nil) -> H
  def coid[H]: H -> (H ::: Nil)
}

trait MonoidalInstances {

}

//trait MonoidalK[->[_[_],_[_]], ⊙[_[_],_[_],_]] extends AssociativeK[->, ⊙] {
//  type Id[_]
//  def idl  [F[_]]: ⊙[Id, F, *] -> F
//  def idr  [F[_]]: ⊙[F, Id, *] -> F
//  def coidl[F[_]]: F -> ⊙[F, Id, *]
//  def coidr[F[_]]: F -> ⊙[Id, F, *]
//}
//object MonoidalK {
//  trait Aux[->[_[_],_[_]], ⊙[_[_],_[_],_], TC0[_[_]], I[_]] extends MonoidalK[->, ⊙] with AssociativeK.Aux[->, ⊙, TC0] {
//    type Id[⭐] = I[⭐]
//  }
//}
