package io.cosmo.exo.categories

import cats.{Monoid, Semigroup}
import io.cosmo.exo.{<=>, Iso}

trait CSemigroup[->[_,_], ⊙[_,_], A] {
  type TC[_]
  def C: Associative.Aux[->, ⊙, TC]

  def op: (A ⊙ A) -> A
}

object CSemigroup {
  type Aux[->[_,_], ⊙[_,_], ->#[_], A] = CSemigroup[->, ⊙, A] {type TC[a] = ->#[a]}

  def unsafe[->[_,_], ⊙[_,_], A](f: (A ⊙ A) -> A)(implicit
    m: Associative[->, ⊙]
  ): CSemigroup.Aux[->, ⊙, m.TC, A] = new CSemigroup[->, ⊙, A] {type TC[a] = m.TC[a]; val C = m; val op = f}

  implicit def fromCats[A](implicit m: Semigroup[A]): CSemigroup.Aux[* => *, (*, *), Trivial.T1, A] =
    unsafe(p => m.combine(p._1, p._2))

  def toCats[A](implicit m: CSemigroup.Aux[* => *, (*, *), Trivial.T1, A]): Semigroup[A] =
    Semigroup.instance({case (a, b) => m.op((a, b))})

  implicit def isoCats[A]: Semigroup[A] <=> CSemigroup.Aux[* => *, (*, *), Trivial.T1, A] =
    Iso.unsafe(fromCats(_), toCats(_))

}
