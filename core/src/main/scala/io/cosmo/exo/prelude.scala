package io.cosmo.exo

import io.cosmo.exo.categories.functors.ExofunctorSyntax

trait BaseDataAliases {

}

trait AllFunctions
  extends DisjunctionFunctions
     with ConjunctionFunctions

trait AllSyntax
  extends DisjunctionSyntax
     with ConjunctionSyntax
     with IsoSyntax
     with ExofunctorSyntax

trait PreludeLowPriority extends BaseDataAliases

trait syntax extends PreludeLowPriority with AllFunctions with AllSyntax
object syntax extends syntax
