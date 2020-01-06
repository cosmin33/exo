package io.cosmo.exo

import io.cosmo.exo.evidence._

object Void {
  private[exo] trait Tag extends Any

  def absurd[A](v: Nothing): A = v

  val isNotUnit: Void =!= Unit = WeakApart.witness(_.flip.coerce(()))
  implicit val isNotAny:  Void =!= Any  = WeakApart.witness(_.flip.coerce(()))
  implicit val uninhabited: Uninhabited[Void] = Uninhabited.witness(identity[Void])
}
