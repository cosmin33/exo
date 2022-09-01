package io.cosmo.exo.internal

package object any {

  implicit final def anySyntaxMouse[A](oa: A): AnyOps[A] = new AnyOps(oa)

}
