package io.cosmo.exo.categories.functors

import cats._
import io.cosmo.exo.categories._

trait LaxSemigroupal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] { self =>
  def A: Associative[-->, ⊙-]
  def product[A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B]

  def map2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(implicit E: Exo[==>, -->, F]): (F[A] ⊙- F[B]) --> F[C] =
    A.C.andThen(product[A, B], E.map(fn))
  def comap2[==>[_,_], A, B, C](fn: C ==> (A ⊙= B))(implicit E: Exo[Dual[==>,*,*], -->, F]): (F[A] ⊙- F[B]) --> F[C] =
    A.C.andThen(product[A, B], E.map(Dual(fn)))

  def preserveCSemigroup[==>[_,_], M](ma: CSemigroup[==>, ⊙=, M])(implicit E: Exo[==>, -->, F]): CSemigroup[-->, ⊙-, F[M]] =
    CSemigroup.unsafe(map2(ma.op))(A)

  def compose[~~>[_,_], ⊙~[_,_], G[_]](G: LaxSemigroupal[⊙-, ~~>, ⊙~, G])(implicit
    F: Exo[-->, ~~>, G]
  ): LaxSemigroupal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] =
    new LaxSemigroupal[⊙=, ~~>, ⊙~, λ[a => G[F[a]]]] { val A = G.A; def product[A, B] = G.map2(self.product[A, B]) }
}

object LaxSemigroupal extends LaxSemigroupalInstances {
  implicit class OplaxSemigroupalOps[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](l: OplaxSemigroupal[⊙=, -->, ⊙-, F]) {
    def opProduct[A, B]: F[A ⊙= B] --> (F[A] ⊙- F[B]) = l.product[A, B].toFn
    def opcomap2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(implicit
      C: Semicategory[-->], E: Exofunctor[==>, Dual[-->,*,*], F]
    ): F[C] --> (F[A] ⊙- F[B]) = l.map2(fn).toFn
    def opmap2[==>[_,_], A, B, C](fn: C ==> (A ⊙= B))(implicit
      C: Semicategory[-->], E: Exofunctor[Dual[==>,*,*], Dual[-->,*,*], F]
    ): F[C] --> (F[A] ⊙- F[B]) = l.map2(Dual(fn)).toFn
  }
}

import LaxSemigroupalHelpers._
trait LaxSemigroupalInstances extends LaxSemigroupalInstances01 {
  implicit def importSemigroupal[F[_]](implicit S: Semigroupal[F]): LaxSemigroupal[(*,*), * => *, (*,*), F] =
    new ImpLaxSemigroupal[F] { val sem = S }
}

trait LaxSemigroupalInstances01 extends LaxSemigroupalInstances02 {
  implicit def importMonoidal[F[_]](implicit M: InvariantMonoidal[F]): LaxMonoidal[(*,*), * => *, (*,*), F] =
    new ImpLaxMonoidal[F] { val sem = M }
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
  trait ImpLaxSemigroupal[F[_]] extends LaxSemigroupal[(*,*), * => *, (*,*), F] {
    protected def sem: Semigroupal[F]
    def A = implicitly
    def product[A, B] = (sem.product[A, B] _).tupled
  }
  trait ImpLaxMonoidal[F[_]] extends ImpLaxSemigroupal[F] with LaxMonoidal[(*,*), * => *, (*,*), F] {
    protected def sem: InvariantMonoidal[F]
    override def A = implicitly
    type I = Unit
    val id: Unit => F[Unit] = _ => sem.unit
  }
}