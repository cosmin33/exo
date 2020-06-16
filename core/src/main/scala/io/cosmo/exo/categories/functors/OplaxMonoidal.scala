package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{CMonoid, Dual, Monoidal}

/** https://ncatlab.org/nlab/show/oplax+monoidal+functor */
trait OplaxMonoidal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends OplaxSemigroupal[==>, ⊙=, -->, ⊙-, F] {
  type I
  def M1: Monoidal.Aux[Dual[==>,*,*], ⊙=, TC, I]
  def M2: Monoidal.Aux[Dual[-->,*,*], ⊙-, λ[a => TC[F[a]]], F[I]]

  def opId: F[I] => I

  def preserveComonoid[M](ma: CMonoid.Aux[Dual[==>,*,*], ⊙=, TC, I, M])(implicit
    E: Exo.Cov[* => *, F[M] --> *]
  ): CMonoid.Aux[Dual[-->,*,*], ⊙-, λ[a => TC[F[a]]], F[I], F[M]] =
    ??? //CMonoid.unsafe(map(ma.id), Dual(E.map(opProduct[M, M])(map(ma.op))))(M2)

}
