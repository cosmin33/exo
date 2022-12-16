package io.cosmo.exo.categories

import cats.Monoid
import io.cosmo.exo._

trait CMonoid[->[_,_], ⊙[_,_], A] extends CSemigroup[->, ⊙, A] {
  type I
  def C: Monoidal.AuxI[->, ⊙, I]

  def id: I -> A
}

object CMonoid {
  type Aux[->[_,_], ⊙[_,_], A, I0] = CMonoid[->, ⊙, A] {type I = I0}

  def unsafe[->[_,_], ⊙[_,_], A, I0](fe: I0 -> A, f: (A ⊙ A) -> A)(implicit
    m: Monoidal.AuxI[->, ⊙, I0]
  ): CMonoid.Aux[->, ⊙, A, I0] =
    new CMonoid[->, ⊙, A] {type I = I0; val C = m; val id = fe; val op = f}

  def fromSemigroup[->[_,_], ⊙[_,_], A, I0](fe: I0 -> A, s: CSemigroup[->, ⊙, A])(implicit
    m: Monoidal.AuxI[->, ⊙, I0]
  ): CMonoid.Aux[->, ⊙, A, I0] = unsafe(fe, s.op)

  implicit def fromCats[A](implicit m: Monoid[A]): CMonoid.Aux[* => *, (*, *), A, Unit] =
    unsafe((_: Unit) => m.empty, p => m.combine(p._1, p._2))

  implicit def toCats[A](implicit m: CMonoid.Aux[* => *, (*, *), A, Unit]): Monoid[A] =
    Monoid.instance(m.id(()), {case (a, b) => m.op((a, b))})

  implicit def isoCats[A]: Monoid[A] <=> CMonoid.Aux[* => *, (*, *), A, Unit] =
    Iso.unsafe(fromCats(_), toCats(_))

}