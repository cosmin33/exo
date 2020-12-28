package io.cosmo.exo.categories

import io.cosmo.exo.{Iso, categories}

trait Braided[->[_, _], ⊙[_, _]] extends Associative[->, ⊙] {
  def braid[A, B]: ⊙[A, B] -> ⊙[B, A]
  def braid1[A, B]: ⊙[A, B] -> ⊙[B, A] = ???

  private type <->[a, b] = Iso[->, a, b]
  def isoBraid[A, B]: ⊙[A, B] <-> ⊙[B, A] = Iso.unsafe(braid[A, B], braid[B, A])(C)
  def isoBraid1[A: TC, B: TC]: ⊙[A, B] <-> ⊙[B, A] = Iso.unsafe(braid1[A, B], braid1[B, A])(C)
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
