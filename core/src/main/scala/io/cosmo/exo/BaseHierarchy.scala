package io.cosmo.exo

trait BaseHierarchy extends BaseHierarchy.BH0

object BaseHierarchy {
  trait BH0 extends BH1 {
  }

  trait BH1 extends BH2 {
  }

  trait BH2 extends BH3 {
  }

  trait BH3 extends BH4 {
  }

  trait BH4 {}
}