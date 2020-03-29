package io.cosmo.exo.categories

import io.cosmo.exo._

trait Cartesian[->[_, _], ⨂[_, _]] extends Monoidal[->, ⨂] with Symmetric[->, ⨂] {
  def fst[A, B]: ⨂[A, B] -> A
  def snd[A, B]: ⨂[A, B] -> B
  def diag[A]: A -> ⨂[A, A]

  def merge[X, Y, Z](f: X -> Y, g: X -> Z): X -> ⨂[Y, Z] = &&&(f, g)
  def &&&[X, Y, Z](f: X -> Y, g: X -> Z): X -> ⨂[Y, Z]

  def isoCartesian[X, Y, Z]: (X -> Y, X -> Z) <=> (X -> ⨂[Y, Z]) =
    Iso.unsafe(p => &&&(p._1, p._2), fn => (C.andThen(fn, fst[Y, Z]), C.andThen(fn, snd[Y, Z])))
}

object Cartesian {
  type Aux[->[_, _], ⨂[_, _], TC0[_], I] = Cartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }

  trait Proto[->[_, _], ⨂[_, _], TC0[_], I] extends Cartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }

  implicit class CocartesianOps[->[_, _], ⨁[_, _], C[_], I](val self: Cartesian.Aux[Dual[->,*,*], ⨁, C, I]) extends AnyVal {
    def inl[A, B]: A -> ⨁[A, B] = self.fst
    def inr[A, B]: B -> ⨁[A, B] = self.snd
    def codiag[A]: ⨁[A, A] -> A = self.diag
    def |||[X, Y, Z](f: X -> Z, g: Y -> Z): ⨁[X, Y] -> Z = self.&&&(Dual(f), Dual(g))
  }
}

object Cocartesian {
  type Aux[->[_, _], ⨂[_, _], TC0[_], I] = Cocartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }
}

