package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

trait Braided[->[_, _], ⊙[_, _]] extends Associative[->, ⊙]:
  def braid[A: TC, B: TC]: ⊙[A, B] -> ⊙[B, A]

object Braided:
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Braided[->, ⊙] { type TC[a] = TC0[a] }
  type AuxT[->[_, _], ⊙[_, _]] = Aux[->, ⊙, Trivial]
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Braided[->, ⊙] { type TC[a] = TC0[a] }
  
  extension[->[_,_], ⊙[_,_]](a: BraidedK[->, ⊙])
    def braidK[F[_], G[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[F[a], G[a]] -> ⊙[G[a], F[a]]] =
      a.braid[TypeK[F], TypeK[G]].unapply
      
end Braided
