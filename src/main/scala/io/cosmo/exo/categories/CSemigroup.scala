package io.cosmo.exo.categories

import io.cosmo.exo._

trait CSemigroup[->[_,_], ⊙[_,_], A]:
  def C: Associative[->, ⊙]
  def op: (A ⊙ A) -> A

object CSemigroup:
  def unsafe[->[_,_], ⊙[_,_], A](f: (A ⊙ A) -> A)(using m: Associative[->, ⊙]): CSemigroup[->, ⊙, A] =
    new CSemigroup[->, ⊙, A] {val C = m; val op = f}
