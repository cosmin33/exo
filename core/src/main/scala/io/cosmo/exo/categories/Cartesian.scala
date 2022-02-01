package io.cosmo.exo.categories

import io.cosmo.exo._

trait Cartesian[->[_, _], ⨂[_, _]] extends Monoidal[->, ⨂] with Symmetric[->, ⨂] {
  def fst[A: TC, B: TC]: ⨂[A, B] -> A
  def snd[A: TC, B: TC]: ⨂[A, B] -> B
  def diag[A: TC]: A -> ⨂[A, A]

  def merge[A, B, C](f: A -> B, g: A -> C): A -> ⨂[B, C] = &&&(f, g)
  def &&&  [A, B, C](f: A -> B, g: A -> C): A -> ⨂[B, C]
  //def &&&  [X: TC, Y, Z](f: X -> Y, g: X -> Z): X -> ⨂[Y, Z] = C.andThen(diag[X], bifunctor.bimap(f, g))

  def strongFirst [A: TC, B: TC, C: TC](fa: A -> B): ⨂[A, C] -> ⨂[B, C] = &&&(C.andThen(fst[A, C], fa), snd[A, C])
  def strongSecond[A: TC, B: TC, C: TC](fa: A -> B): ⨂[C, A] -> ⨂[C, B] = &&&(fst[C, A], C.andThen(snd[C, A], fa))

  def isoCartesian[A, B: TC, C: TC]: (A -> B, A -> C) <=> (A -> ⨂[B, C]) =
    Iso.unsafe(p => &&&(p._1, p._2), fn => (C.andThen(fn, fst[B, C]), C.andThen(fn, snd[B, C])))
}

object Cartesian {
  type Aux[->[_, _], ⨂[_, _], TC0[_], I] = Cartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }
  def apply[->[_, _], ⨂[_, _]](implicit c: Cartesian[->, ⨂]): Cartesian.Aux[->, ⨂, c.TC, c.Id] = c

  implicit class CocartesianOps[->[_, _], ⨁[_, _], TC[_], I](val self: Cartesian.Aux[Dual[->,*,*], ⨁, TC, I]) extends AnyVal {
    def inl[A: TC, B: TC]: A -> ⨁[A, B] = self.fst
    def inr[A: TC, B: TC]: B -> ⨁[A, B] = self.snd
    def codiag[A: TC]: ⨁[A, A] -> A = self.diag
    def split[A, B, C](f: A -> C, g: B -> C): ⨁[A, B] -> C = |||(f, g)
    def |||  [A, B, C](f: A -> C, g: B -> C): ⨁[A, B] -> C = self.&&&(Dual(f), Dual(g))
    def isoCocartesian[A: TC, B: TC, C]: (A -> C, B -> C) <=> (⨁[A, B] -> C) =
      Iso.unsafe(
        p => |||(p._1, p._2),
        fn => (self.C.andThen(Dual(fn), self.fst[A, B]), self.C.andThen(Dual(fn), self.snd[A, B]))
      )
  }
}

object Cocartesian {
  type Aux[->[_, _], ⨂[_, _], TC0[_], I] = Cocartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }
  def apply[->[_, _], ⨂[_, _]](implicit c: Cartesian[Dual[->,*,*], ⨂]): Cartesian.Aux[Dual[->,*,*], ⨂, c.TC, c.Id] = c
}

