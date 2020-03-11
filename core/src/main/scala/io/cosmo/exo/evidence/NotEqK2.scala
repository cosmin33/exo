package io.cosmo.exo.evidence

class NotEqK2[F[_,_], G[_,_]]

object NotEqK2 {
  implicit def neq[F[_,_], G[_,_]]: F NotEqK2 G = null
  @scala.annotation.implicitAmbiguous("Could not prove that ${F} not equal to ${F}")
  implicit def neqAmbig1[F[_,_]]: F NotEqK2 F = null
  implicit def neqAmbig2[F[_,_]]: F NotEqK2 F = null
}