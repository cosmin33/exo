package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories
import io.cosmo.exo.categories.{Associative, CMonoid, CSemigroup, Dual, Monoidal}

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[==>, ⊙=, -->, ⊙-, F] { self =>
  type I
  def M1: Monoidal.Aux[==>, ⊙=, TC, I]
  def M2: Monoidal.Aux[-->, ⊙-, λ[a => TC[F[a]]], F[I]]

  def id: I --> F[I]

  def preserveCMonoid[M](ma: CMonoid.Aux[==>, ⊙=, TC, I, M]): CMonoid.Aux[-->, ⊙-, λ[a => TC[F[a]]], F[I], F[M]] =
    CMonoid.unsafe(map(ma.id), map2(ma.op))(M2)

}

object LaxMonoidal {
  type Endo[->[_, _], ⊙[_, _], F[_]] = LaxMonoidal[->, ⊙, ->, ⊙, F]
  type Con[==>[_,_], ⊙[_,_], -->[_,_], ∪[_,_], F[_]] = LaxMonoidal[Dual[==>,*,*], ⊙, -->, ∪, F]

  implicit class ColaxMonoidalOps[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](
    val self: LaxMonoidal[Dual[==>,*,*], ⊙=, -->, ⊙-, F]
  ) extends AnyVal {
    def comap2[A, B, C](fn: C ==> (A ⊙= B))(implicit E: Exo.Con[* => *, * --> F[C]]): (F[A] ⊙- F[B]) --> F[C] =
      ??? //E.map(Dual(self.product[A, B]))(self.map[A ⊙= B, C](Dual(fn)))
  }

}
