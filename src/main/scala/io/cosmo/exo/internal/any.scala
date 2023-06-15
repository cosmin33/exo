package io.cosmo.exo.internal

private[exo] object any:
  extension [A](a: A)
    inline def |>[B](f: A => B): B = f(a)
    def asLeft[B]: Either[A, B] = Left(a)
    def asRight[B]: Either[B, A] = Right(a)
