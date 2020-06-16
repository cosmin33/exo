package io.cosmo.exo.categories.functors

import io.cosmo.exo
import io.cosmo.exo.categories
import io.cosmo.exo.categories.{Associative, CSemigroup, Dual, Monoidal}

trait OplaxSemigroupal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends Exofunctor[Dual[==>,*,*], Dual[-->,*,*], F] {
  type TC[_]

  def M1: Associative.Aux[Dual[==>,*,*], ⊙=, TC]
  def M2: Associative.Aux[Dual[-->,*,*], ⊙-, λ[a => TC[F[a]]]]

  def opProduct[A, B]: F[A ⊙= B] --> (F[A] ⊙- F[B])

  def opmap2[A, B, C](fn: C ==> (A ⊙= B))(implicit E: Exo.Cov[* => *, F[C] --> *]): F[C] --> (F[A] ⊙- F[B]) =
    {
      val mm: Dual[-->, F[A ⊙= B], F[C]] = map[A ⊙= B, C](Dual(fn))
      val pp: Dual[-->, F[A] ⊙- F[B], F[A ⊙= B]] = Dual(opProduct[A, B])
      val m1: F[C] --> F[A ⊙= B] = mm.toFn
      val p1: F[A ⊙= B] --> (F[A] ⊙- F[B]) = pp.toFn
      //val r1 = M2.C.andThen(m1, p1)
      //val rr = M2.C.andThen(mm, pp).toFn
      //M2.C.andThen(map[A ⊙= B, C](Dual(fn)), Dual.apply(opProduct[A, B]))
      ???
    }
//  def opmap2[A, B, C](fn: C ==> (A ⊙= B))(implicit E: Exo.Cov[* => *, F[C] --> *]): F[C] --> (F[A] ⊙- F[B]) =
//    E.map(opProduct[A, B])(map[A ⊙= B, C](Dual(fn)).toFn)

  def preserveCosemigroup[M](ma: CSemigroup.Aux[Dual[==>,*,*], ⊙=, TC, M])(implicit
    E: Exo.Cov[* => *, F[M] --> *]
  ): CSemigroup.Aux[Dual[-->,*,*], ⊙-, λ[a => TC[F[a]]], F[M]] =
    ??? //CSemigroup.unsafe(Dual(E.map(opProduct[M, M])(map(ma.op))))(M2)
}
