package io.cosmo.exo.functors

/** https://ncatlab.org/nlab/show/Frobenius+monoidal+functor */
trait FrobeniusMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]]:
  def functor:     LaxMonoidal[⊙=, -->, ⊙-, F]
  def opFunctor: OplaxMonoidal[⊙=, -->, ⊙-, F]

  def product  [A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B] = functor.product[A, B]
  def opProduct[A, B]: F[A ⊙= B] --> (F[A] ⊙- F[B]) = opFunctor.opProduct[A, B]
