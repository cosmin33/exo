package io.cosmo.exo.categories.functors

import cats.implicits._
import io.cosmo.exo.categories.{Associative, CMonoid, CSemigroup, Dual, Monoidal}

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[==>, ⊙=, -->, ⊙-, F] {
  self =>
  type I
  def M1: Monoidal.Aux[==>, ⊙=, TC1, I]
  def M2: Monoidal.Aux[-->, ⊙-, TC2, F[I]]

  def id: I => F[I]

  def preserveCMonoid[M](ma: CMonoid.Aux[==>, ⊙=, TC1, I, M]): CMonoid.Aux[-->, ⊙-, TC2, F[I], F[M]] =
    CMonoid.unsafe1(map(ma.id), map2(ma.op))(M2)

  def compose[~~>[_, _], ⊙~[_, _], ~>#[_], G[_]](G: LaxMonoidal.Aux[-->, ⊙-, ~~>, ⊙~, TC2, ~>#, F[I], G]
  ) =
    new LaxMonoidal[==>, ⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] {
      type I = self.I
      type TC1[a] = self.TC1[a]
      type TC2[a] = G.TC2[a]
      def M1: Monoidal.Aux[==>, ⊙=, TC1, I] = self.M1
      def M2: Monoidal.Aux[~~>, ⊙~, ~>#, G[F[I]]] = G.M2
      def id: I => G[F[I]] = self.id >>> G.id
      def product[A, B] = M2.C.andThen(G.product[F[A], F[B]], G.map(self.product[A, B]))
      def map[A, B](f: A ==> B) = G.map(self.map(f))
    }
}

object LaxMonoidal {
  type Aux[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], =>#[_], ->#[_], I0, F[_]] =
    LaxMonoidal[==>, ⊙=, -->, ⊙-, F] { type I = I0; type TC1[a] = =>#[a]; type TC2[a] = ->#[a] }
  type Endo[->[_,_], ⊙[_,_], F[_]] = LaxMonoidal[->, ⊙, ->, ⊙, F]
}
