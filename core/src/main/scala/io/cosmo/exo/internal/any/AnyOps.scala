package io.cosmo.exo.internal.any

final class AnyOps[A](private val a: A) extends AnyVal {
  @inline def |>[B](f: A => B): B = f(a)
}
