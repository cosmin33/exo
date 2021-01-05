package io.cosmo.exo.categories

import cats.Monoid
import io.cosmo.exo._

trait CMonoid[->[_,_], ⊙[_,_], A] extends CSemigroup[->, ⊙, A] {
  type TC[_]
  type I
  def C: Monoidal.Aux[->, ⊙, TC, I]

  def id: I -> A
  def op: (A ⊙ A) -> A
}

object CMonoid {
  type Aux[->[_,_], ⊙[_,_], ->#[_], I0, A] = CMonoid[->, ⊙, A] {type TC[a] = ->#[a]; type I = I0}
  type AuxI[->[_,_], ⊙[_,_], I0, A] = CMonoid[->, ⊙, A] {type I = I0}

  def unsafe[->[_,_], ⊙[_,_], A, ->#[_], I0](fe: I0 -> A, f: (A ⊙ A) -> A)(implicit
    m: Monoidal.Aux[->, ⊙, ->#, I0]
  ): CMonoid.Aux[->, ⊙, ->#, I0, A] =
    new CMonoid[->, ⊙, A] {type TC[a] = ->#[a]; type I = I0; val C = m; val id = fe; val op = f}

  def unsafe1[->[_,_], ⊙[_,_], A, I0](fe: I0 -> A, f: (A ⊙ A) -> A)(implicit
    m: Monoidal.AuxI[->, ⊙, I0]
  ) =
    new CMonoid[->, ⊙, A] {type TC[a] = m.TC[a]; type I = I0; val C = m; val id = fe; val op = f}

  def fromSemigroup[->[_,_], ⊙[_,_], A, ->#[_], I0](fe: I0 -> A, s: CSemigroup.Aux[->, ⊙, ->#, A])(implicit
    m: Monoidal.Aux[->, ⊙, ->#, I0]
  ): CMonoid.Aux[->, ⊙, ->#, I0, A] =
    new CMonoid[->, ⊙, A] {type TC[x] = ->#[x]; type I = I0; val C = m; val id = fe; val op = s.op}

  implicit def fromCats[A](implicit m: Monoid[A]): CMonoid.Aux[* => *, (*, *), Trivial.T1, Unit, A] =
    unsafe((_: Unit) => m.empty, p => m.combine(p._1, p._2))

  implicit def toCats[A](implicit m: CMonoid.Aux[* => *, (*, *), Trivial.T1, Unit, A]): Monoid[A] =
    Monoid.instance(m.id(()), {case (a, b) => m.op((a, b))})

  implicit def isoCats[A]: Monoid[A] <=> CMonoid.Aux[* => *, (*, *), Trivial.T1, Unit, A] =
    Iso.unsafe(fromCats(_), toCats(_))

}