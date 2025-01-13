package io.cosmo.exo.categories

import io.cosmo.exo.*

class AssociativeTest {
  summon[Associative[* => *, Tuple2]]
  summon[Associative.Aux[* => *, Tuple2, Trivial]]

  summon[AssociativeK.Aux[* => *, Tuple2, TrivialK]]
  summon[BraidedK.Aux[* => *, Tuple2, TrivialK]]
  summon[SymmetricK.Aux[* => *, Tuple2, TrivialK]]
  summon[MonoidalK.Aux[* => *, Tuple2, TrivialK, UnitK]]
  summon[CartesianK.Aux[* => *, Tuple2, TrivialK, UnitK]]
  summon[CccK.Aux[* => *, Tuple2, * => *, TrivialK, UnitK]]

  summon[AssociativeK2.Aux[* => *, Tuple2, TrivialK2]]
  summon[BraidedK2.Aux[* => *, Tuple2, TrivialK2]]
  summon[SymmetricK2.Aux[* => *, Tuple2, TrivialK2]]
  summon[MonoidalK2.Aux[* => *, Tuple2, TrivialK2, UnitK2]]
  summon[CartesianK2.Aux[* => *, Tuple2, TrivialK2, UnitK2]]
  summon[CccK2.Aux[* => *, Tuple2, * => *, TrivialK2, UnitK2]]

  summon[AssociativeH.Aux[* => *, Tuple2, TrivialH]]
  summon[BraidedH.Aux[* => *, Tuple2, TrivialH]]
  summon[SymmetricH.Aux[* => *, Tuple2, TrivialH]]
  summon[MonoidalH.Aux[* => *, Tuple2, TrivialH, UnitH]]
  summon[CartesianH.Aux[* => *, Tuple2, TrivialH, UnitH]]
  summon[CccH.Aux[* => *, Tuple2, * => *, TrivialH, UnitH]]

}
