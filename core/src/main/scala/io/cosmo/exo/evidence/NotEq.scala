package io.cosmo.exo.evidence

/** Inequality, as defined in shapeless */
class NotEq[A, B]

object NotEq {
  implicit def neq[A, B]: A =:!= B = null
  @scala.annotation.implicitAmbiguous("Could not prove that ${A} =:!= ${A}")
  implicit def neqAmbig1[A]: A =:!= A = null
  implicit def neqAmbig2[A]: A =:!= A = null
}
