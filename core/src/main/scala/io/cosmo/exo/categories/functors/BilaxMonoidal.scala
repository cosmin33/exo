package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{Braided, Monoidal}

/** https://ncatlab.org/nlab/show/bilax+monoidal+functor */
trait BilaxMonoidal[==>[_,_], ⊙[_,_], -->[_,_], ∪[_,_], F[_]] extends StrongMonoidal[==>, ⊙, -->, ∪, F] {
//  def M1: Monoidal[==>, ⊙] with Braided[==>, ⊙]
//  def M2: Monoidal[-->, ∪] with Braided[-->, ∪]
}
