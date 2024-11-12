package io.cosmo.exo

import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*

object ArrowKTest {
  type Fuk[A, B] = ArrowK[Function, A, B]
  /////////////////// Bifunctor ///////////////////
  summon[Endobifunctor[ArrowK[* => *,*,*], Tuple2]]

  /////////////////// Subcategory Hierarchy ///////////////////
  summon[Semicategory[Fuk]]
  summon[Subcat.Aux[Fuk, IsKind]]
  summon[Distributive.Aux[Fuk, IsKind, Tuple2, TypeK[[a] =>> Unit], Either, TypeK[[a] =>> Void]]]

  /////////////////// Associative Hierarchy ///////////////////
  summon[Associative.Aux[Fuk, Tuple2, IsKind]]
  summon[Associative.Aux[Dual[ArrowK[Function,*,*],*,*], Either, IsKind]]
  summon[Braided.Aux[Fuk, Tuple2, IsKind]]
  summon[Braided.Aux[Dual[ArrowK[Function,*,*],*,*], Either, IsKind]]
  summon[Symmetric.Aux[Fuk, Tuple2, IsKind]]
  summon[Symmetric.Aux[Dual[ArrowK[Function,*,*],*,*], Either, IsKind]]
  summon[Monoidal.Aux[Fuk, Tuple2, IsKind, TypeK[[a] =>> Unit]]]
  summon[Monoidal.Aux[Dual[ArrowK[Function,*,*],*,*], Either, IsKind, TypeK[[a] =>> Void]]]
  summon[Cartesian.Aux[Fuk, Tuple2, IsKind, TypeK[[a] =>> Unit]]]
  summon[Cocartesian.Aux[Fuk, Either, IsKind, TypeK[[a] =>> Void]]]
  summon[Ccc.Aux[Fuk, Tuple2, Function, IsKind, TypeK[[a] =>> Unit]]]
  summon[Ccc.Aux[Fuk, Tuple2, Fuk, IsKind, TypeK[[a] =>> Unit]]]

  summon[AssociativeK[Function, Tuple2]]
  summon[CoAssociativeK[Function, Either]]
  summon[BraidedK[Function, Tuple2]]
  summon[CoBraidedK[Function, Either]]
  summon[SymmetricK[Function, Tuple2]]
  summon[CoSymmetricK[Function, Either]]
  summon[MonoidalK.Aux[Function, Tuple2, [a] =>> Unit]]
  summon[CoMonoidalK.Aux[Function, Either, [a] =>> Void]]
  summon[CartesianK.Aux[Function, Tuple2, [a] =>> Unit]]
  summon[CocartesianK.Aux[Function, Either, [a] =>> Void]]
  summon[CccK.Aux[Function, Tuple2, [a] =>> Unit]]

  /////////////////// Initial, Terminal ///////////////////
  summon[Initial.Aux[Fuk, IsKind, TypeK[[a] =>> Void]]]
  summon[Terminal.Aux[Fuk, IsKind, TypeK[[a] =>> Unit]]]

  summon[InitialK[Function]]
  summon[InitialK.Aux[Function, [a] =>> Void]]
  summon[TerminalK[Function]]
  summon[TerminalK.Aux[Function, [a] =>> Unit]]

}
