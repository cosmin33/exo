package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.typeclasses.HasTc

package object functors {

  type Exo[==>[_,_], -->[_,_], F[_]] = Exofunctor[==>, -->, F]
  val Exo = Exofunctor

  type ExoRepr[==>[_,_], -->[_,_], F[_]] = ∃[λ[R => (Exofunctor[==>, -->, F], ∀[λ[x => Iso[==>, R --> x, F[x]]]])]]
  type Repr[->[_,_], F[_]] = ExoRepr[->, ->, F]

  type OplaxSemigroupal[=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxSemigroupal[=⊙, Dual[-->,*,*], -⊙, F]
  type OplaxMonoidal   [=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxMonoidal   [=⊙, Dual[-->,*,*], -⊙, F]

  type StrongSemigroupal[=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxSemigroupal[=⊙, Iso[-->,*,*], -⊙, F]
  type StrongMonoidal   [=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxMonoidal   [=⊙, Iso[-->,*,*], -⊙, F]

  type IsoFunctor[F[_]] = Exo[Iso[* => *,*,*], * => *, F]

  type FunctorK[H[_[_]]] = Exo[FunK, * => *, HasTc[H, *]]
  object FunctorK {
    def apply[H[_[_]]](implicit F: FunctorK[H]): FunctorK[H] = F
    trait Proto[H[_[_]]] extends FunctorK[H] {
      def map[A, B](f: FunK[A, B]): HasTc[H, A] => HasTc[H, B] = HasTc.isoFun1(f.kindA, f.kindB).flip(mapK(f.fn))
      protected def mapK[F[_], G[_]](f: F ~> G): H[F] => H[G]
    }
  }

  type CovariantK[H[_[_]]] = Exo[Dual[FunK,*,*], * => *, HasTc[H, *]]
  object CofunctorK {
    def apply[H[_[_]]](implicit F: CovariantK[H]): CovariantK[H] = F
    trait Proto[H[_[_]]] extends CovariantK[H] {
      def map[A, B](f: Dual[FunK, A, B]): HasTc[H, A] => HasTc[H, B] = {
        val fn = f.toFn
        HasTc.isoFun1[H, A, fn.TypeB, B, fn.TypeA](fn.kindB, fn.kindA).flip(comapK(fn.fn))
      }
      protected def comapK[F[_], G[_]](f: G ~> F): H[F] => H[G]
    }
  }

  type IsoFunctorK[H[_[_]]] = Exo[IsoFunK, * => *, HasTc[H, *]]
  object IsoFunctorK {
    def apply[H[_[_]]](implicit F: IsoFunctorK[H]): IsoFunctorK[H] = F
    trait Proto[H[_[_]]] extends IsoFunctorK[H] {
      def map[A, B](i: IsoFunK[A, B]): HasTc[H, A] => HasTc[H, B] = {
        val ito = i.to
        val isok: ito.TypeA <~> ito.TypeB = FunK.isoFunKUnapply(i)(ito.kindA, ito.kindB)
        HasTc.isoFun1(ito.kindA, ito.kindB).flip(mapK(isok))
      }
      protected def mapK[F[_], G[_]](f: F <~> G): H[F] => H[G]
    }
  }

}
