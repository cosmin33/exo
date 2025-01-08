package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._

trait LaxSemigroupalK[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_]]]:
  type TC[_]
  def A: Associative.Aux[-->, ⊙-, TC]
  def product[F[_], G[_]]: (A[F] ⊙- A[G]) --> A[[a] =>> F[a] ⊙= G[a]]

  def map2[==>[_,_], F[_], G[_], H[_]](fn: ∀[[a] =>> F[a] ⊙= G[a] ==> H[a]])(using E: ExoK[==>, -->, A]): (A[F] ⊙- A[G]) --> A[H] =
    A.C.andThen(product[F, G], E.map(fn))
  def comap2[==>[_,_], F[_], G[_], H[_]](fn: ∀[[a] =>> H[a] ==> F[a] ⊙= G[a]])(using E: ExoK[Dual[==>,*,*], -->, A]): (A[F] ⊙- A[G]) --> A[H] =
    A.C.andThen(product[F, G], E.map(Dual.forall[==>, [a] =>> F[a] ⊙= G[a], H](fn)))

  def preserveCSemigroup[==>[_,_], M[_]](ma: CSemigroupK[==>, ⊙=, M])(using E: ExoK[==>, -->, A]): CSemigroup[-->, ⊙-, A[M]] =
    CSemigroup.unsafe(map2(ma.op))(using A)

object LaxSemigroupalK:
  def apply[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_]]](using l: LaxSemigroupalK[⊙=, -->, ⊙-, A]): LaxSemigroupalK[⊙=, -->, ⊙-, A] = l
  extension[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_]]](l: OplaxSemigroupalK[⊙=, -->, ⊙-, A])
    def opProduct[F[_], G[_]]: A[[a] =>> F[a] ⊙= G[a]] --> (A[F] ⊙- A[G]) = l.product[F, G]
    def opcomap2[==>[_,_], F[_], G[_], H[_]](fn: ∀[[a] =>> (F[a] ⊙= G[a]) ==> H[a]])(using
      C: Semicategory[-->], E: ExofunctorK[==>, Dual[-->,*,*], A]
    ): A[H] --> (A[F] ⊙- A[G]) = l.map2(fn)
    def opmap2[==>[_,_], F[_], G[_], H[_]](fn: ∀[[a] =>> H[a] ==> (F[a] ⊙= G[a])])(using
      C: Semicategory[-->], E: ExofunctorK[Dual[==>,*,*], Dual[-->,*,*], A]
    ): A[H] --> (A[F] ⊙- A[G]) = l.map2(Dual.forall[==>, [a] =>> F[a] ⊙= G[a], H](fn))

