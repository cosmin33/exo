package io.cosmo.exo

import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*

object ArrowKTest {
  /////////////////// Bifunctor ///////////////////
  summon[Endobifunctor[ArrowK[* => *,*,*], Tuple2]]

  /////////////////// Subcategory Hierarchy ///////////////////
  summon[Semicategory[ArrowK[Function,*,*]]]
  summon[Subcat.Aux[ArrowK[Function,*,*], IsKind]]
  summon[Distributive.Aux[ArrowK[Function,*,*], IsKind, Tuple2, TypeK[[a] =>> Unit], Either, TypeK[[a] =>> Void]]]

  /////////////////// Associative Hierarchy ///////////////////
  summon[Associative.Aux[ArrowK[Function,*,*], Tuple2, IsKind]]
  summon[Braided.Aux[ArrowK[Function,*,*], Tuple2, IsKind]]
  summon[Braided.Aux[Dual[ArrowK[Function1,*,*],*,*], Either, IsKind]]
  summon[Symmetric.Aux[ArrowK[Function,*,*], Tuple2, IsKind]]
  summon[Symmetric.Aux[Dual[ArrowK[Function1,*,*],*,*], Either, IsKind]]
  summon[Monoidal.Aux[ArrowK[Function,*,*], Tuple2, IsKind, TypeK[[a] =>> Unit]]]
  summon[Monoidal.Aux[Dual[ArrowK[Function1,*,*],*,*], Either, IsKind, TypeK[[a] =>> Void]]]
  summon[Cartesian.Aux[ArrowK[Function,*,*], Tuple2, IsKind, TypeK[[a] =>> Unit]]]
  summon[Cocartesian.Aux[ArrowK[Function,*,*], Either, IsKind, TypeK[[a] =>> Void]]]
  summon[Ccc.Aux[ArrowK[Function,*,*], Tuple2, Function, IsKind, TypeK[[a] =>> Unit]]]
  summon[Ccc.Aux[ArrowK[Function,*,*], Tuple2, ArrowK[Function,*,*], IsKind, TypeK[[a] =>> Unit]]]

  /////////////////// Initial, Terminal ///////////////////
  summon[Initial.Aux[ArrowK[Function,*,*], IsKind, TypeK[[a] =>> Void]]]
  summon[Terminal.Aux[ArrowK[Function,*,*], IsKind, TypeK[[a] =>> Unit]]]

}
