package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{CMonoid, Monoidal}

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[⊙=, -->, ⊙-, F] { self =>
  def A: Monoidal.AuxI[-->, ⊙-, I]
  type I
  def id: I --> F[I]

  def preserveCMonoid[==>[_,_], TC2[_], M](ma: CMonoid.Aux[==>, ⊙=, I, M])(implicit E: Exo[==>, -->, F]): CMonoid.Aux[-->, ⊙-, I, F[M]] =
    CMonoid.unsafe(A.C.andThen(id, E.map(ma.id)), map2(ma.op))(A)

  def compose[~~>[_,_], ⊙~[_,_], G[_]](
    G: LaxMonoidal.Aux[⊙-, ~~>, ⊙~, I, G]
  )(implicit
    E: Exo[-->, ~~>, G]
  ): LaxMonoidal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] =
    new LaxMonoidal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] {
      type I = self.I
      def A = G.A
      def id = G.A.C.andThen(G.id, E.map(self.id))
      def product[A, B] = G.map2(self.product[A, B])
    }
}

object LaxMonoidal {
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], I0, F[_]] = LaxMonoidal[⊙=, -->, ⊙-, F] { type I = I0 }
}
