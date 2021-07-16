package io.cosmo.exo.categories

import cats.{Monoid, Semigroup}
import io.cosmo.exo.{<=>, Iso}

trait CSemigroup[->[_,_], ⊙[_,_], A] {
  def C: Associative[->, ⊙]

  def op: (A ⊙ A) -> A
}

object CSemigroup {
  def unsafe[->[_,_], ⊙[_,_], A](f: (A ⊙ A) -> A)(implicit
    m: Associative[->, ⊙]
  ): CSemigroup[->, ⊙, A] = new CSemigroup[->, ⊙, A] {val C = m; val op = f}

  implicit def fromCats[A](implicit m: Semigroup[A]): CSemigroup[* => *, (*, *), A] =
    unsafe((m.combine _).tupled)

  def toCats[A](implicit m: CSemigroup[* => *, (*, *), A]): Semigroup[A] =
    Semigroup.instance({case (a, b) => m.op((a, b))})

  implicit def isoCats[A]: Semigroup[A] <=> CSemigroup[* => *, (*, *), A] =
    Iso.unsafe(fromCats(_), toCats(_))

}
