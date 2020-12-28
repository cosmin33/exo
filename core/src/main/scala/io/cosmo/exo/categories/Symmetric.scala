package io.cosmo.exo.categories

trait Symmetric[->[_, _], ⊙[_, _]] extends Braided[->, ⊙] {
  def swap[A, B]: ⊙[A, B] -> ⊙[B, A] = braid
  def swap1[A: TC, B: TC]: ⊙[A, B] -> ⊙[B, A] = braid1
}
object Symmetric {
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Symmetric[->, ⊙] {type TC[a] = TC0[a]}
  type AuxT[->[_, _], ⊙[_, _]] = Aux[->, ⊙, Trivial.T1]
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Symmetric[->, ⊙] { type TC[a] = TC0[a] }
}

//trait SymmetricK[->[_[_],_[_]], ⊙[_[_],_[_],_]] extends BraidedK[->, ⊙] {
//  def swap[F[_], G[_]]: ⊙[F, G, ?] -> ⊙[G, F, ?] = braid
//}
//object SymmetricK {
//  trait Aux[->[_[_],_[_]], ⊙[_[_],_[_],_], TC0[_[_]]] extends SymmetricK[->, ⊙] with BraidedK.Aux[->, ⊙, TC0]
//}