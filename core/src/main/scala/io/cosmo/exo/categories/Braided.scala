package io.cosmo.exo.categories

import io.cosmo.exo._

trait Braided[->[_, _], ⊙[_, _]] extends Associative[->, ⊙]:
  def braid[A: TC, B: TC]: ⊙[A, B] -> ⊙[B, A]

object Braided:
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Braided[->, ⊙] { type TC[a] = TC0[a] }
  type AuxT[->[_, _], ⊙[_, _]] = Aux[->, ⊙, Trivial]
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Braided[->, ⊙] { type TC[a] = TC0[a] }
end Braided
