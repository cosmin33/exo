package io.cosmo.exo.categories

//trait AllFunctions

trait AllSyntax
  extends SubcategorySyntax

trait BaseHierarchyLowPriority extends BaseHierarchy

trait syntax extends BaseHierarchyLowPriority with /*AllFunctions with*/ AllSyntax
object syntax extends syntax

trait BaseHierarchy extends BaseHierarchy.BH0 {

}

object BaseHierarchy {
  trait BH0 extends BH1 {

  }
  trait BH1 extends BH2 {
  }
  trait BH2 extends BH3 {

  }
  trait BH3 extends BH4
  trait BH4 extends BH5
  trait BH5
}