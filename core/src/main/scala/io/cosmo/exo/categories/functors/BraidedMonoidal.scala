package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{Braided, Monoidal}

trait BraidedMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxMonoidal[⊙=, -->, ⊙-, F] {
}
