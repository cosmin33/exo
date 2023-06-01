package io.cosmo.exo.instances

import io.cosmo.exo.categories.{Symmetric, *}
import io.cosmo.exo.*

object DualInstancesTest {
  summon[Semicategory[Dual[Function,*,*]]]
  summon[Subcat[Dual[Function,*,*]]]
  summon[Braided[Dual[Function,*,*], Tuple2]]
  summon[Symmetric[Dual[Function,*,*], Tuple2]]
  summon[Monoidal[Dual[Function,*,*], Tuple2]]
}
