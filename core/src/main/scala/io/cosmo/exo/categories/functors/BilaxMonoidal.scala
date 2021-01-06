package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.Dual

/** https://ncatlab.org/nlab/show/bilax+monoidal+functor */
trait BilaxMonoidal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends Exofunctor[==>, -->, F]  {
  def functor: BraidedMonoidal[==>, ⊙=, -->, ⊙-, F]
  def opFunctor: BraidedMonoidal[Dual[==>,*,*], ⊙=, Dual[-->,*,*], ⊙-, F]

  def product[A, B]: F[A] ⊙- F[B] --> F[A ⊙= B] = functor.product[A, B]
  def opProduct[A, B]: F[A ⊙= B] --> (F[A] ⊙- F[B]) = opFunctor.opProduct[A, B]
  // TODO: Laws
}
