package io.cosmo.exo.categories.functors

import io.cosmo
import io.cosmo.exo
import io.cosmo.exo.categories
import io.cosmo.exo.categories.{Associative, CSemigroup, Dual, Monoidal}

trait OplaxSemigroupal[==>[_,_], ⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends Exofunctor[Dual[==>,*,*], Dual[-->,*,*], F] {
  type TC[_]

  def M1: Associative.Aux[Dual[==>,*,*], ⊙=, TC]
  def M2: Associative.Aux[Dual[-->,*,*], ⊙-, λ[a => TC[F[a]]]]

  def opProduct[A, B]: F[A ⊙= B] --> (F[A] ⊙- F[B])

  def opmap2[A, B, C](fn: C ==> (A ⊙= B)): F[C] --> (F[A] ⊙- F[B]) =
    M2.C.andThen(Dual(opProduct[A, B]), map(Dual(fn))).toFn

  def preserveCosemigroup[M](ma: CSemigroup.Aux[Dual[==>,*,*], ⊙=, TC, M])
  : CSemigroup.Aux[Dual[-->,*,*], ⊙-, λ[a => TC[F[a]]], F[M]] =
    CSemigroup.unsafe(Dual(opmap2(ma.op.toFn)))(M2)
}
