package io.cosmo.exo.categories.functors

import cats._
import io.cosmo.exo.categories._

trait LaxSemigroupal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] { self =>
  def A: Associative[-->, ⊙-]
  def product[A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B]

  def map2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(implicit E: Exo[==>, -->, F]): (F[A] ⊙- F[B]) --> F[C] =
    A.C.andThen(product[A, B], E.map(fn))

  def preserveCSemigroup[==>[_,_], M](ma: CSemigroup[==>, ⊙=, M])(implicit E: Exo[==>, -->, F]): CSemigroup[-->, ⊙-, F[M]] =
    CSemigroup.unsafe(map2(ma.op))(A)

  def compose[~~>[_,_], ⊙~[_,_], ~>#[_], G[_]](
    G: LaxSemigroupal[⊙-, ~~>, ⊙~, G]
  )(implicit S: Associative[~~>, ⊙~], F: Exo[-->, ~~>, G]): LaxSemigroupal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] =
    new LaxSemigroupal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] {
      def A = S
      def product[A, B]: (G[F[A]] ⊙~ G[F[B]]) ~~> G[F[A ⊙= B]] = G.map2(self.product[A, B])
    }
}

object LaxSemigroupal extends LaxSemigroupalInstances {
  implicit class OplaxSemigroupalOps[=⊙[_,_], -->[_,_], -⊙[_,_], F[_]](l: OplaxSemigroupal[=⊙, -->, -⊙, F]) {
    def opProduct[A, B]: F[A =⊙ B] --> (F[A] -⊙ F[B]) = l.product[A, B].toFn
    def opmap2[==>[_,_], A, B, C](fn: C ==> (A =⊙ B))(implicit
      C: Semicategory[-->], E: Exofunctor[Dual[==>,*,*], Dual[-->,*,*], F]
    ): F[C] --> (F[A] -⊙ F[B]) = l.map2(Dual(fn)).toFn
  }
}

trait LaxSemigroupalInstances extends LaxSemigroupalInstances01 {
  implicit def importSemigroupal[F[_]](implicit S: Semigroupal[F]): LaxSemigroupal[(*,*), * => *, (*,*), F] =
    new LaxSemigroupal[(*,*), * => *, (*,*), F] {
      def A: Associative[Function, Tuple2] = implicitly
      def product[A, B] = (S.product[A, B] _).tupled
    }
}

trait LaxSemigroupalInstances01 extends LaxSemigroupalInstances02 {
  implicit def importMonoidal[F[_]](implicit M: InvariantMonoidal[F]): LaxMonoidal[(*,*), * => *, (*,*), F] =
    new LaxMonoidal[(*,*), * => *, (*,*), F] {
      def A = implicitly
      type I1 = Unit
      type I2 = Unit
      def id = _ => M.unit
      def product[A, B] = (M.product[A, B] _).tupled
    }
}

trait LaxSemigroupalInstances02 extends LaxSemigroupalInstances03{
}

trait LaxSemigroupalInstances03 extends LaxSemigroupalInstances04 {
}

trait LaxSemigroupalInstances04 extends LaxSemigroupalInstances05 {
}

trait LaxSemigroupalInstances05 {

}

private object LaxSemigroupalHelpers {
}