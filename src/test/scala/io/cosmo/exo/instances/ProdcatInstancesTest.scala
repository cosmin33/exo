package io.cosmo.exo.instances

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*

object ProdcatInstancesTest {
  summon[Distributive.Aux[Prodcat[Function1, Function1, *, *], Trivial, /\, Unit, \/, Void]]
  summon[Groupoid.Aux[Prodcat[===, ===, *, *], Trivial]]
  summon[Subcategory.Aux[Prodcat[===, <~<, *, *], Trivial]]
  summon[Semicategory[Prodcat[===, <~<, *, *]]]

  summon[Endobifunctor[Prodcat[===, ===, *, *], &]]

  summon[Ccc.Aux[Prodcat[Function1, Function1, *, *], Tuple2, Trivial, Unit, Function1]]
  summon[Cartesian.Aux[Prodcat[Function1, Function1, *, *], Tuple2, Trivial, Unit]]
  summon[Monoidal.Aux[Prodcat[Function1, Function1, *, *], Tuple2, Trivial, Unit]]
  summon[Symmetric.Aux[Prodcat[===, ===, *, *], &, Trivial]]
  summon[Braided.Aux[Prodcat[===, ===, *, *], &, Trivial]]
  summon[Associative.Aux[Prodcat[===, ===, *, *], &, Trivial]]

  summon[Initial.Aux[Prodcat[Function1, Function1, *, *], Trivial, Void]]
  summon[Terminal.Aux[Prodcat[Function1, Function1, *, *], Trivial, Unit]]
}
