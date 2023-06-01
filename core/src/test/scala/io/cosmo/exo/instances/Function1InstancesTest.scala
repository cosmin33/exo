package io.cosmo.exo.instances

import io.cosmo.exo.*
import io.cosmo.exo.categories.{Distributive, *}

object Function1InstancesTest {
  summon[Subcat[Function]]
  summon[Ccc[Function]]
  summon[Distributive[Function, Tuple2, Either]]
  summon[Distributive[Function, /\, \/]]
  summon[Initial[Function]]
  summon[Terminal[Function]]
}
