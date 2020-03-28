package io.cosmo.exo.categories.functors

import cats.{Applicative, ContravariantMonoidal, InvariantSemigroupal, InvariantMonoidal}
import io.cosmo.exo.{<=>, Iso, ~>}
import io.cosmo.exo.categories.{Associative, Braided, Dual, Endobifunctor, Monoidal, Subcat, CMonoid}
import io.cosmo.exo.categories.Trivial
import io.cosmo.exo.evidence.{=~=, =~~=}

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[==>, ⊙=, -->, ⊙-, F] { self =>
  type TC[_]
  type I
  def M1: Monoidal.Aux[==>, ⊙=, TC, I]
  def M2: Monoidal.Aux[-->, ⊙-, λ[a => TC[F[a]]], F[I]]

  def preserveMonoid[M](ma: CMonoid.Aux[==>, ⊙=, TC, I, M])(implicit
    E: Exo.Con[* => *, * --> F[M]]
  ): CMonoid.Aux[-->, ⊙-, λ[a => TC[F[a]]], F[I], F[M]] =
    CMonoid.unsafe(map(ma.id), E.map(Dual(product[M, M]))(map(ma.op)))(M2)

}

object LaxMonoidal {
  type Endo[->[_, _], ⊙[_, _], F[_]] = LaxMonoidal[->, ⊙, ->, ⊙, F]
  type Con[==>[_,_], ⊙[_,_], -->[_,_], ∪[_,_], F[_]] = LaxMonoidal[Dual[==>,*,*], ⊙, -->, ∪, F]

  implicit class ColaxMonoidalOps[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](
    val self: LaxMonoidal[Dual[==>,*,*], ⊙=, -->, ⊙-, F]
  ) extends AnyVal {
    def comap2[A, B, C](fn: C ==> (A ⊙= B))(implicit E: Exo.Con[* => *, * --> F[C]]): (F[A] ⊙- F[B]) --> F[C] =
      E.map(Dual(self.product[A, B]))(self.map[A ⊙= B, C](Dual(fn)))
  }

}
