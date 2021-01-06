package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{Braided, Monoidal}

trait BraidedMonoidal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxMonoidal[==>, ⊙=, -->, ⊙-, F] {
  def M1: Monoidal.Aux[==>, ⊙=, TC1, I1] with Braided.Aux[==>, ⊙=, TC1]
  def M2: Monoidal.Aux[-->, ⊙-, TC2, I2] with Braided.Aux[-->, ⊙-, TC2]
}
