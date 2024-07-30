package io.cosmo.exo.instances

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

object Function1InstancesTest {
  /////////////////// Subcategory Hierarchy ///////////////////
  summon[Semicategory[Function]]
  summon[Semicategory[Dual[Function,*,*]]]
  summon[Semicategory[Opp[Function]]]
  summon[Subcat.Aux[Function, Trivial]]
  summon[Subcat.Aux[Dual[Function,*,*], Trivial]]
  summon[Subcat.Aux[Opp[Function], Trivial]]
  summon[Distributive.Aux[Function, Trivial, Tuple2, Unit, Either, Void]]
  summon[Distributive.Aux[Function, Trivial, /\, Unit, \/, Void]]
  
  /////////////////// Associative Hierarchy ///////////////////
  summon[Associative.Aux[Function, Tuple2, Trivial]]
  summon[Braided.Aux[Function, Tuple2, Trivial]]
  summon[Symmetric.Aux[Function, Tuple2, Trivial]]
  summon[Monoidal.Aux[Function, Tuple2, Trivial, Unit]]
  summon[Cartesian.Aux[Function, Tuple2, Trivial, Unit]]
  summon[Ccc.Aux[Function, Tuple2, Trivial, Unit, Function]]

  summon[Associative.Aux[Dual[Function,*,*], Tuple2, Trivial]]
  summon[Braided.Aux[Dual[Function,*,*], Tuple2, Trivial]]
  summon[Symmetric.Aux[Dual[Function,*,*], Tuple2, Trivial]]
  summon[Monoidal.Aux[Dual[Function,*,*], Tuple2, Trivial, Unit]]

  summon[Associative.Aux[Opp[Function], Tuple2, Trivial]]
  summon[Braided.Aux[Opp[Function], Tuple2, Trivial]]
  summon[Symmetric.Aux[Opp[Function], Tuple2, Trivial]]
  summon[Monoidal.Aux[Opp[Function], Tuple2, Trivial, Unit]]

  summon[Associative.Aux[Function, /\, Trivial]]
  summon[Braided.Aux[Function, /\, Trivial]]
  summon[Symmetric.Aux[Function, /\, Trivial]]
  summon[Monoidal.Aux[Function, /\, Trivial, Unit]]
  summon[Cartesian.Aux[Function, /\, Trivial, Unit]]
  summon[Ccc.Aux[Function, /\, Trivial, Unit, Function]]

  summon[Associative.Aux[Dual[Function,*,*], /\, Trivial]]
  summon[Braided.Aux[Dual[Function,*,*], /\, Trivial]]
  summon[Symmetric.Aux[Dual[Function,*,*], /\, Trivial]]
  summon[Monoidal.Aux[Dual[Function,*,*], /\, Trivial, Unit]]

  summon[Associative.Aux[Opp[Function], /\, Trivial]]
  summon[Braided.Aux[Opp[Function], /\, Trivial]]
  summon[Symmetric.Aux[Opp[Function], /\, Trivial]]
  summon[Monoidal.Aux[Opp[Function], /\, Trivial, Unit]]

  summon[Associative.Aux[Dual[Function,*,*], Either, Trivial]]
  summon[Braided.Aux[Dual[Function,*,*], Either, Trivial]]
  summon[Symmetric.Aux[Dual[Function,*,*], Either, Trivial]]
  summon[Monoidal.Aux[Dual[Function,*,*], Either, Trivial, Void]]
  summon[Cocartesian.Aux[Function, Either, Trivial, Void]]

  summon[Associative.Aux[Opp[Function], Either, Trivial]]
  summon[Braided.Aux[Opp[Function], Either, Trivial]]
  summon[Symmetric.Aux[Opp[Function], Either, Trivial]]
  summon[Monoidal.Aux[Opp[Function], Either, Trivial, Void]]
  summon[Cartesian.Aux[Opp[Function], Either, Trivial, Void]]

  summon[Associative.Aux[Function, Either, Trivial]]
  summon[Braided.Aux[Function, Either, Trivial]]
  summon[Symmetric.Aux[Function, Either, Trivial]]
  summon[Monoidal.Aux[Function, Either, Trivial, Void]]

  summon[Associative.Aux[Dual[Function,*,*], \/, Trivial]]
  summon[Braided.Aux[Dual[Function,*,*], \/, Trivial]]
  summon[Symmetric.Aux[Dual[Function,*,*], \/, Trivial]]
  summon[Monoidal.Aux[Dual[Function,*,*], \/, Trivial, Void]]
  summon[Cocartesian.Aux[Function, \/, Trivial, Void]]

  summon[Associative.Aux[Opp[Function], \/, Trivial]]
  summon[Braided.Aux[Opp[Function], \/, Trivial]]
  summon[Symmetric.Aux[Opp[Function], \/, Trivial]]
  summon[Monoidal.Aux[Opp[Function], \/, Trivial, Void]]
  summon[Cartesian.Aux[Opp[Function], \/, Trivial, Void]]

  summon[Associative.Aux[Function, \/, Trivial]]
  summon[Braided.Aux[Function, \/, Trivial]]
  summon[Symmetric.Aux[Function, \/, Trivial]]
  summon[Monoidal.Aux[Function, \/, Trivial, Void]]

  /////////////////// Initial, Terminal ///////////////////
  summon[Initial[Function]]
  summon[Terminal[Function]]
}
