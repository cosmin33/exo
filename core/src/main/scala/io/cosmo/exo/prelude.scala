package io.cosmo.exo

trait BaseDataAliases {

}

trait AllFunctions
  extends DisjunctionFunctions
     with ConjunctionFunctions

trait AllSyntax
  extends DisjunctionSyntax
     with ConjunctionSyntax
     with IsoSyntax

trait PreludeLowPriority extends BaseHierarchy with BaseDataAliases

trait syntax extends PreludeLowPriority with AllFunctions with AllSyntax
object syntax extends syntax
