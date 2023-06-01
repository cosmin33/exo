package io.cosmo.exo.functors

import io.cosmo.exo.categories._

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[⊙=, -->, ⊙-, F] { self =>
  def A: Monoidal.Aux[-->, ⊙-, TC, I]
  type I
  def id: I --> F[I]

  def preserveCMonoid[==>[_,_], TC2[_], M](ma: CMonoid.Aux[==>, ⊙=, M, I])(using
    E: Exo[==>, -->, F]
  ): CMonoid.Aux[-->, ⊙-, F[M], I] =
    CMonoid.unsafe(A.C.andThen(id, E.map(ma.id)), map2(ma.op))(using A)

  def compose[~~>[_,_], ⊙~[_,_], TC0[_], G[_]](G: LaxMonoidal.Aux[⊙-, ~~>, ⊙~, TC0, I, G])(using
    E: Exo[-->, ~~>, G]
  ): LaxMonoidal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] =
    new LaxMonoidal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] {
      type I = self.I
      type TC[a] = TC0[a]
      def A = G.A
      def id = G.A.C.andThen(G.id, E.map(self.id))
      def product[A, B] = G.map2(self.product[A, B])
    }
  
}

object LaxMonoidal:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], TC0[_], I0, F[_]] = LaxMonoidal[⊙=, -->, ⊙-, F] { type TC[a] = TC0[a]; type I = I0 }
