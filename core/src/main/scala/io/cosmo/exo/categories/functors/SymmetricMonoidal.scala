package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{Monoidal, Symmetric}

trait SymmetricMonoidal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxMonoidal[==>, ⊙=, -->, ⊙-, F] {
  def M1: Monoidal.Aux[==>, ⊙=, TC1, I1] with Symmetric.Aux[==>, ⊙=, TC1]
  def M2: Monoidal.Aux[-->, ⊙-, TC2, I2] with Symmetric.Aux[-->, ⊙-, TC2]
}
