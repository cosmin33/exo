package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[⊙=, -->, ⊙-, F]:
  self =>
  type ID
  def D: Monoidal.Aux[-->, ⊙-, TD, ID]
  def id: ID --> F[ID]
  
  def preserveCMonoid[==>[_,_], TC2[_], M](ma: CMonoid.Aux[==>, ⊙=, M, ID])(using
    E: Exo[==>, -->, F]
  ): CMonoid.Aux[-->, ⊙-, F[M], ID] =
    CMonoid.unsafe(D.C.andThen(id, E.map(ma.id)), map2(ma.op))(using D)

  def compose[~~>[_,_], ⊙~[_,_], TD0[_], G[_]](G: LaxMonoidal.Aux[⊙-, ~~>, ⊙~, TD0, ID, G])(using
    E: Exo[-->, ~~>, G]
  ): LaxMonoidal.Aux[⊙=, ~~>, ⊙~, TD0, ID, [a] =>> G[F[a]]] =
    new LaxMonoidal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]]:
      type ID = self.ID
      type TD[a] = TD0[a]
      def D = G.D
      def id = G.D.C.andThen(G.id, E.map(self.id))
      def product[A, B]: G[F[A]] ⊙~ G[F[B]] ~~> G[F[A ⊙= B]] = G.map2(self.product[A, B])

object LaxMonoidal:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, F[_]] = LaxMonoidal[⊙=, -->, ⊙-, F] { type TD[a] = C[a]; type ID = I0 }

/////////////////////////////////////////////////////////////////

trait LaxSemigroupal1[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]]:
  self =>
  type TC[_]
  type TD[_]
  def C: Associative.Aux[==>, ⊙=, TC]
  def D: Associative.Aux[-->, ⊙-, TD]
  def F: Exo[==>, -->, F]
  def product[A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B]

  def map2[A, B, C](fn: (A ⊙= B) ==> C): (F[A] ⊙- F[B]) --> F[C] =
    D.C.andThen(product[A, B], F.map(fn))

  def preserveCSemigroup[M](ma: CSemigroup[==>, ⊙=, M]): CSemigroup[-->, ⊙-, F[M]] =
    CSemigroup.unsafe(map2(ma.op))(using D)

  def compose[~~>[_,_], ⊙~[_,_], G[_]](G: LaxSemigroupal1[-->, ⊙-, ~~>, ⊙~, G])(using F1: Exo[-->, ~~>, G]
  ): LaxSemigroupal1[==>, ⊙=, ~~>, ⊙~, [a] =>> G[F[a]]] =
    new LaxSemigroupal1[==>, ⊙=, ~~>, ⊙~, [a] =>> G[F[a]]]:
      type TC[a] = self.TC[a]
      type TD[a] = G.TD[a]
      val C: Associative.Aux[==>, ⊙=, TC] = self.C
      val D: Associative.Aux[~~>, ⊙~, TD] = G.D
      val F: Exo[==>, ~~>, [a] =>> G[F[a]]] = self.F.compose(F1)
      def product[A, B]: G[F[A]] ⊙~ G[F[B]] ~~> G[F[A ⊙= B]] = G.map2(self.product[A, B])

trait LaxMonoidal1[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal1[==>, ⊙=, -->, ⊙-, F]:
  self =>
  type IC
  type ID
  def C: Monoidal.Aux[==>, ⊙=, TC, IC]
  def D: Monoidal.Aux[-->, ⊙-, TD, ID]
  def id: ID --> F[IC]

  def preserveCMonoid[M](ma: CMonoid.Aux[==>, ⊙=, M, IC]): CMonoid.Aux[-->, ⊙-, F[M], ID] =
    CMonoid.unsafe(D.C.andThen(id, F.map(ma.id)), map2(ma.op))(using D)

  def compose[~~>[_,_], ⊙~[_,_], TC0[_], G[_]](that: LaxMonoidal1[-->, ⊙-, ~~>, ⊙~, G] {type IC = self.ID})(using
    F1: Exo[-->, ~~>, G]
  ): LaxMonoidal1[==>, ⊙=, ~~>, ⊙~, [a] =>> G[F[a]]] =
    new LaxMonoidal1[==>, ⊙=, ~~>, ⊙~, [a] =>> G[F[a]]]:
      type TC[a] = self.TC[a]
      type TD[a] = that.TD[a]
      type IC = self.IC
      type ID = that.ID
      val C: Monoidal.Aux[==>, ⊙=, TC, IC] = self.C
      val D: Monoidal.Aux[~~>, ⊙~, TD, ID] = that.D
      val F: Exo[==>, ~~>, [a] =>> G[F[a]]] = self.F.compose(F1)
      def id: ID ~~> G[F[IC]] = D.C.andThen(that.id, F1.map(self.id))
      def product[A, B]: G[F[A]] ⊙~ G[F[B]] ~~> G[F[A ⊙= B]] = that.map2(self.product[A, B])
object LaxMonoidal1:
  type Aux[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], IC0, ID0, F[_]] =
    LaxMonoidal1[==>, ⊙=, -->, ⊙-, F] { type TC[a] = C[a]; type IC = IC0; type ID = ID0 }
