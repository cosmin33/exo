package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._

trait LaxSemigroupalK2[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_,_]]]:
  type TC[_]
  def A: Associative.Aux[-->, ⊙-, TC]
  def product[F[_,_], G[_,_]]: (A[F] ⊙- A[G]) --> A[[a, b] =>> F[a, b] ⊙= G[a, b]]

  def map2[==>[_,_], F[_,_], G[_,_], H[_,_]](fn: ∀∀[[a, b] =>> F[a, b] ⊙= G[a, b] ==> H[a, b]])(using E: ExoK2[==>, -->, A]): (A[F] ⊙- A[G]) --> A[H] =
    A.C.andThen(product[F, G], E.map(fn))
  def comap2[==>[_,_], F[_,_], G[_,_], H[_,_]](fn: ∀∀[[a, b] =>> H[a, b] ==> F[a, b] ⊙= G[a, b]])(using E: ExoK2[Dual[==>,*,*], -->, A]): (A[F] ⊙- A[G]) --> A[H] =
    A.C.andThen(product[F, G], E.map(Dual.forall2[==>, [a, b] =>> F[a, b] ⊙= G[a, b], H](fn)))

  def preserveCSemigroup[==>[_,_], M[_,_]](ma: CSemigroupK2[==>, ⊙=, M])(using E: ExoK2[==>, -->, A]): CSemigroup[-->, ⊙-, A[M]] =
    CSemigroup.unsafe(map2(ma.op))(using A)

object LaxSemigroupalK2:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], A[_[_,_]]] = LaxSemigroupalK2[⊙=, -->, ⊙-, A] { type TC[a] = C[a] }
  def apply[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_,_]]](using l: LaxSemigroupalK2[⊙=, -->, ⊙-, A]): LaxSemigroupalK2[⊙=, -->, ⊙-, A] = l
  extension[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_,_]]](l: OplaxSemigroupalK2[⊙=, -->, ⊙-, A])
    def opProduct[F[_,_], G[_,_]]: A[[a, b] =>> F[a, b] ⊙= G[a, b]] --> (A[F] ⊙- A[G]) = l.product[F, G]
    def opcomap2[==>[_,_], F[_,_], G[_,_], H[_,_]](fn: ∀∀[[a, b] =>> (F[a, b] ⊙= G[a, b]) ==> H[a, b]])(using
      Semicategory[-->], ExofunctorK2[==>, Dual[-->,*,*], A]
    ): A[H] --> (A[F] ⊙- A[G]) = l.map2(fn)
    def opmap2[==>[_,_], F[_,_], G[_,_], H[_,_]](fn: ∀∀[[a, b] =>> H[a, b] ==> (F[a, b] ⊙= G[a, b])])(using
      Semicategory[-->], ExofunctorK2[Dual[==>,*,*], Dual[-->,*,*], A]
    ): A[H] --> (A[F] ⊙- A[G]) = l.map2(Dual.forall2[==>, [a, b] =>> F[a, b] ⊙= G[a, b], H](fn))
  
  trait Proto[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], A[_[_,_]]] extends LaxSemigroupalK2[⊙=, -->, ⊙-, A]:
    type TC[a] = C[a]
