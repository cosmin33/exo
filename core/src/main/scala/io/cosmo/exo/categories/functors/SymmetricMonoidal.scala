package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{Monoidal, Symmetric}

trait SymmetricMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxMonoidal[⊙=, -->, ⊙-, F] {
}
