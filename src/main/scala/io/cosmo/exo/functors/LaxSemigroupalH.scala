package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._

trait LaxSemigroupalH[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_[_]]]] {
  type TC[_]
  def A: Associative.Aux[-->, ⊙-, TC]
  def product[F[_[_]], G[_[_]]]: (A[F] ⊙- A[G]) --> A[[a[_]] =>> F[a] ⊙= G[a]]

  def map2[==>[_,_], F[_[_]], G[_[_]], H[_[_]]](fn: ∀~[[a[_]] =>> F[a] ⊙= G[a] ==> H[a]])(using E: ExoH[==>, -->, A]): (A[F] ⊙- A[G]) --> A[H] =
    A.C.andThen(product[F, G], E.map(fn))
  def comap2[==>[_,_], F[_[_]], G[_[_]], H[_[_]]](fn: ∀~[[a[_]] =>> H[a] ==> F[a] ⊙= G[a]])(using E: ExoH[Dual[==>,*,*], -->, A]): (A[F] ⊙- A[G]) --> A[H] =
    A.C.andThen(product[F, G], E.map(Dual.forallK[==>, [a[_]] =>> F[a] ⊙= G[a], H](fn)))

  def preserveCSemigroup[==>[_,_], M[_[_]]](ma: CSemigroupH[==>, ⊙=, M])(using E: ExoH[==>, -->, A]): CSemigroup[-->, ⊙-, A[M]] =
    CSemigroup.unsafe(map2(ma.op))(using A)
}

object LaxSemigroupalH:
  def apply[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_[_]]]](using l: LaxSemigroupalH[⊙=, -->, ⊙-, A]): LaxSemigroupalH[⊙=, -->, ⊙-, A] = l
  extension[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_[_]]]](l: OplaxSemigroupalH[⊙=, -->, ⊙-, A])
    def opProduct[F[_[_]], G[_[_]]]: A[[a[_]] =>> F[a] ⊙= G[a]] --> (A[F] ⊙- A[G]) = l.product[F, G]
    def opcomap2[==>[_,_], F[_[_]], G[_[_]], H[_[_]]](fn: ∀~[[a[_]] =>> (F[a] ⊙= G[a]) ==> H[a]])(using
      Semicategory[-->], ExofunctorH[==>, Dual[-->,*,*], A]
    ): A[H] --> (A[F] ⊙- A[G]) = l.map2(fn)
    def opmap2[==>[_,_], F[_[_]], G[_[_]], H[_[_]]](fn: ∀~[[a[_]] =>> H[a] ==> (F[a] ⊙= G[a])])(using
      Semicategory[-->], ExofunctorH[Dual[==>,*,*], Dual[-->,*,*], A]
    ): A[H] --> (A[F] ⊙- A[G]) = l.map2(Dual.forallK[==>, [a[_]] =>> F[a] ⊙= G[a], H](fn))
