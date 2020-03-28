package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{Dual, Monoidal}

/** https://ncatlab.org/nlab/show/oplax+monoidal+functor */
trait OplaxMonoidal[==>[_,_], ⊙[_,_], -->[_,_], ∪[_,_], F[_]] extends Exofunctor[Dual[==>,*,*], Dual[-->,*,*], F] {
  def M1: Monoidal[==>, ⊙]
  def M2: Monoidal[-->, ∪]

  def product[A, B]: F[A ⊙ B] => (F[A] ∪ F[B])

  def opmap2[A, B, C](fn: C ==> (A ⊙ B))(implicit E: Exo.Cov[* => *, F[C] --> *]): F[C] --> (F[A] ∪ F[B]) =
    E.map(product[A, B])(map[A ⊙ B, C](Dual(fn)).toFn)
}
