package io.cosmo.exo


trait ProdK[F[_], G[_]] {
  type Pivot <: Any
  type Need[_] <: Any
  def tc: Need[Pivot]

  val _1: F[Pivot]
  val _2: G[Pivot]
}

object ProdK {
  type Aux[F[_], G[_], A] = ProdK[F, G] {type Pivot = A}
  def apply[F[_], G[_], A](f: F[A], g: G[A]): ProdK.Aux[F, G, A] = new ProdK[F, G] {
    override type Pivot = A
    override type Need[a] = Unit
    def tc: Need[A] = ()
    override val _1: F[A] = f
    override val _2: G[A] = g
  }


}


// from a scalaz John de Goes's comment in: https://github.com/scalaz/scalaz/issues/1526
trait Productive[F[_]] {
  def product[A, B](fa: F[A], fb: F[B]): F[(A, B)]
  def unit: F[Unit]
}
trait Coproductive[F[_]] {
  def coproduct[A, B](fa: F[A], fb: F[B]): F[A \/ B]
  def counit: F[Void]
}
