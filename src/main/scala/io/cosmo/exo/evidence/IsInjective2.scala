package io.cosmo.exo.evidence

import io.cosmo.exo.internal._
import io.cosmo.exo._

trait IsInjective2[F[_,_]] {

  def apply[A, B, X, Y](using ev: F[A, B] === F[X, Y]): (A === X, B === Y)

}

object IsInjective2 {

  def apply[F[_,_]](using ev: IsInjective2[F]): IsInjective2[F] = ev

  def witness1[F[_,_], A, B, X](using ev1: F[A, X] =!= F[B, X], ev2: F[X, A] =!= F[X, B]): IsInjective2[F] =
    new IsInjective2[F] {
      // it seems like it can be proved (see IsInjective.witness1) but I don't know how
      def apply[A1, B1, X1, Y1](using ev1: F[A1, B1] === F[X1, Y1]): (A1 === X1, B1 === Y1) =
        (Unsafe.is, Unsafe.is)
    }

  given tuple:       IsInjective2[Tuple2] = witness1[Tuple2, 1, 2, 3]
  given either:      IsInjective2[Either] = witness1[Either, 1, 2, 3]
  given conjunction: IsInjective2[/\]     = witness1[/\, 1, 2, 3]
  given disjunction: IsInjective2[\/]     = witness1[\/, 1, 2, 3]
  given funK:        IsInjective2[FunK]   = witness1[FunK, 1, 2, 3]

}