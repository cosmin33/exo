package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.Monoidal
import io.cosmo.exo.{<=>, Iso}

/** https://cstheory.stackexchange.com/questions/12412/explaining-applicative-functor-in-categorical-terms-monoidal-functors */
trait StrongMonoidal[==>[_,_], ⊙[_,_], -->[_,_], ∪[_,_], F[_]] extends LaxMonoidal[==>, ⊙, -->, ∪, F] {
//  def M1: Monoidal[==>, ⊙]
//  def M2: Monoidal[-->, ∪]
//
//  def invProduct[A, B]: F[A ∪ B] => (F[A] ⊙ F[B])
//
//  //def iso[A, B]: (F[A] ⊙ F[B]) <=> F[A ∪ B] = Iso.unsafe(product, invProduct)
}

object StrongMonoidal {
  type Endo[->[_,_], ⊙[_, _], F[_]] = StrongMonoidal[->, ⊙, ->, ⊙, F]
}