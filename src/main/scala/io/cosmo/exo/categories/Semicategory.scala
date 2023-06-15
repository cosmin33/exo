package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.internal._

trait Semicategory[->[_,_]]:
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C

object Semicategory
  extends Function1SemicategoryInstances
  with DualSemicategoryInstances
  with EvidenceCatSubcatInstances:
  
  def apply[->[_,_]](using ev: Semicategory[->]): Semicategory[->] = ev

end Semicategory
