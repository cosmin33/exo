package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[⊙=, -->, ⊙-, F]:
  self =>
  type ID
  type IC
  def D: Monoidal.Aux[-->, ⊙-, TD, ID]
  def id: ID --> F[IC]

  def preserveCMonoid[==>[_,_], M](ma: CMonoid.Aux[==>, ⊙=, M, IC])(using
    E: Exo[==>, -->, F]
  ): CMonoid.Aux[-->, ⊙-, F[M], ID] =
    CMonoid.unsafe(D.C.andThen(id, E.map(ma.id)), map2(ma.op))(using D)

  def compose[~~>[_,_], ⊙~[_,_], G[_]](that: LaxMonoidal[⊙-, ~~>, ⊙~, G] {type IC = self.ID})(using
    E: Exo[-->, ~~>, G]
  ): LaxMonoidal.Aux[⊙=, ~~>, ⊙~, that.TD, that.ID, self.IC, [a] =>> G[F[a]]] =
    new LaxMonoidal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]]:
      type TD[a] = that.TD[a]
      type IC = self.IC
      type ID = that.ID
      val D: Monoidal.Aux[~~>, ⊙~, TD, ID] = that.D
      def id: ID ~~> G[F[IC]] = D.C.andThen(that.id, E.map(self.id))
      def product[A, B]: G[F[A]] ⊙~ G[F[B]] ~~> G[F[A ⊙= B]] = that.map2(self.product[A, B])

object LaxMonoidal:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], TD0[_], ID0, IC0, F[_]] = LaxMonoidal[⊙=, -->, ⊙-, F]: 
    type TD[a] = TD0[a]
    type ID = ID0
    type IC = IC0
