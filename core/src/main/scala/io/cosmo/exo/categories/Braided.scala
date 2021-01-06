package io.cosmo.exo.categories

trait Braided[->[_, _], ⊙[_, _]] extends Associative[->, ⊙] {
  def braid[A: TC, B: TC]: ⊙[A, B] -> ⊙[B, A]
}

object Braided {
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Braided[->, ⊙] { type TC[a] = TC0[a] }
  type AuxT[->[_, _], ⊙[_, _]] = Aux[->, ⊙, Trivial.T1]
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Braided[->, ⊙] { type TC[a] = TC0[a] }

}

//trait BraidedK[->[_[_],_[_]], ⊙[_[_],_[_],_]] extends AssociativeK[->, ⊙] {
//  def braid[F[_], G[_]]: ⊙[F, G, ?] -> ⊙[G, F, ?]
//}
//object BraidedK {
//  trait Aux[->[_[_],_[_]], ⊙[_[_],_[_],_], TC0[_[_]]] extends BraidedK[->, ⊙] with AssociativeK.Aux[->, ⊙, TC0]
//}
