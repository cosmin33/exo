package io.cosmo.exo.categories.data

import cats.implicits._
import io.cosmo.exo.categories.{Subcat, Trivial}

final case class DeductionCat[T[_], A, B](fn: T[A] => T[B])

object DeductionCat {
  implicit def category[T[_]]: Subcat.Aux[DeductionCat[T,*,*], Trivial.T1] =
    new Subcat[DeductionCat[T,*,*]] {
      type TC[a] = Trivial.T1[a]
      def id[A](implicit A: TC[A]): DeductionCat[T, A, A] = DeductionCat(identity)
      def andThen[A, B, C](ab: DeductionCat[T, A, B], bc: DeductionCat[T, B, C]): DeductionCat[T, A, C] =
        DeductionCat(ab.fn >>> bc.fn)
    }
}
