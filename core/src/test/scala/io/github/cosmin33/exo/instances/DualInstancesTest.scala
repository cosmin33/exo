package io.github.cosmin33.exo.instances

import io.github.cosmin33.exo.categories.*
import io.github.cosmin33.exo.*

object DualInstancesTest {
  summon[Semicategory[Dual[Function,*,*]]]
  summon[Subcat[Dual[Function,*,*]]]
  summon[Braided[Dual[Function,*,*], Tuple2]]
  summon[Symmetric[Dual[Function,*,*], Tuple2]]
  summon[Monoidal[Dual[Function,*,*], Tuple2]]
}
