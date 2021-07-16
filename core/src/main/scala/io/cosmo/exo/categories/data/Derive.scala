package io.cosmo.exo.categories.data

/** A recipe for constructing a `TC[F[A]]` instance given a `TC[A]` */
trait Derive[F[_], TC[_]] {
  def derive[A: TC]: TC[F[A]]
}

object Derive {
  def apply[F[_], TC[_]](implicit d: Derive[F, TC]): Derive[F, TC] = d
}