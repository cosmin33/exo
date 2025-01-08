package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[⊙=, -->, ⊙-, F]:
  self =>
  type I
  def A: Monoidal.Aux[-->, ⊙-, TC, I]
  def id: I --> F[I]
  
  def preserveCMonoid[==>[_,_], TC2[_], M](ma: CMonoid.Aux[==>, ⊙=, M, I])(using
    E: Exo[==>, -->, F]
  ): CMonoid.Aux[-->, ⊙-, F[M], I] =
    CMonoid.unsafe(A.C.andThen(id, E.map(ma.id)), map2(ma.op))(using A)

  def compose[~~>[_,_], ⊙~[_,_], TC0[_], G[_]](G: LaxMonoidal.Aux[⊙-, ~~>, ⊙~, TC0, I, G])(using
    E: Exo[-->, ~~>, G]
  ): LaxMonoidal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]] =
    new LaxMonoidal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]]:
      type I = self.I
      type TC[a] = TC0[a]
      def A = G.A
      def id = G.A.C.andThen(G.id, E.map(self.id))
      def product[A, B] = G.map2(self.product[A, B])


object LaxMonoidal:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, F[_]] = LaxMonoidal[⊙=, -->, ⊙-, F] { type TC[a] = C[a]; type I = I0 }
