package io.cosmo.exo.categories

import io.cosmo.exo.*

class AssociativeTest {
  summon[Associative[* => *, Tuple2]]
  summon[Associative.Aux[* => *, Tuple2, Trivial]]

  summon[AssociativeK[* => *, Tuple2]]
  summon[BraidedK[* => *, Tuple2]]
  summon[MonoidalK[* => *, Tuple2]]
  summon[SymmetricK[* => *, Tuple2]]
  summon[CartesianK[* => *, Tuple2]]
  summon[CccK[* => *, Tuple2, * => *]]

  summon[AssociativeK2[* => *, Tuple2]]
  summon[BraidedK2[* => *, Tuple2]]
  summon[MonoidalK2[* => *, Tuple2]]
  summon[SymmetricK2[* => *, Tuple2]]
  summon[CartesianK2[* => *, Tuple2]]
  summon[CccK2[* => *, Tuple2, * => *]]

}
