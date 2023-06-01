package io.cosmo.exo.categories

import io.cosmo.exo._

trait CMonoid[->[_,_], ⊙[_,_], A] extends CSemigroup[->, ⊙, A]:
  type I
  def C: Monoidal.AuxI[->, ⊙, I]
  def id: I -> A

object CMonoid:
  type Aux[->[_,_], ⊙[_,_], A, I0] = CMonoid[->, ⊙, A] {type I = I0}

  def unsafe[->[_,_], ⊙[_,_], A, I0](fe: I0 -> A, f: (A ⊙ A) -> A)(using m: Monoidal.AuxI[->, ⊙, I0]
  ): CMonoid.Aux[->, ⊙, A, I0] =
    new CMonoid[->, ⊙, A] {type I = I0; val C = m; val id = fe; val op = f}

  def fromSemigroup[->[_,_], ⊙[_,_], A, I0](fe: I0 -> A, s: CSemigroup[->, ⊙, A])(using m: Monoidal.AuxI[->, ⊙, I0]
  ): CMonoid.Aux[->, ⊙, A, I0] = unsafe(fe, s.op)
end CMonoid
