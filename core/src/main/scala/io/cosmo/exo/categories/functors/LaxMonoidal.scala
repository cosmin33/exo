package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{CMonoid, Dual, Monoidal}

/** https://ncatlab.org/nlab/show/monoidal+functor */
trait LaxMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[⊙=, -->, ⊙-, F] { self =>
  type I1
  type I2

  def id: I2 --> F[I1]

//  def preserveCMonoid[M](ma: CMonoid.Aux[==>, ⊙=, TC1, I1, M]): CMonoid.Aux[-->, ⊙-, TC2, I2, F[M]] =
//    CMonoid.unsafe(M2.C.andThen(id, map(ma.id)), map2(ma.op))(M2)

//  def compose[~~>[_, _], ⊙~[_, _], TC3[_], I3, G[_]](G: LaxMonoidal.Aux[-->, ⊙-, TC2, I2, ~~>, ⊙~, TC3, I3, G]
//  ) =
//    new LaxMonoidal[==>, ⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] {
//      type I1 = self.I1
//      type I2 = I3
//      type TC1[a] = self.TC1[a]
//      type TC2[a] = TC3[a]
//      def M1: Monoidal.Aux[==>, ⊙=, TC1, I1] = self.M1
//      def M2: Monoidal.Aux[~~>, ⊙~, TC3, I2] = G.M2
//      def id: I2 ~~> G[F[I1]] = M2.C.andThen(G.id, G.map(self.id))
//      def product[A, B]: G[F[A]] ⊙~ G[F[B]] ~~> G[F[A ⊙= B]] = G.map2(self.product[A, B])
//      def map[A, B](f: A ==> B): G[F[A]] ~~> G[F[B]] = G.map(self.map(f))
//    }
}

object LaxMonoidal {
//  implicit class OplaxMonoidalOps[==>[_,_], =⊙[_,_], I10, -->[_,_], -⊙[_,_], I20, F[_]](
//    l: OplaxMonoidal[==>, =⊙, -->, -⊙, F] { type I1 = I10; type I2 = I20 }
//  ) {
//    def opId: F[I10] --> I20 = l.id.toFn
//  }

}
