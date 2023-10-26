package io.cosmo.exo.functors

import io.cosmo.exo.categories._
import io.cosmo.exo._

type Exo[==>[_, _], -->[_, _], F[_]] = Exofunctor[==>, -->, F]
val Exo = Exofunctor

type Endofunctor[->[_,_], F[_]] = Exofunctor[->, ->, F]
object Endofunctor:
  /** This is isomorphic to cats.Functor[F] */
  type CovF[F[_]] = Endofunctor[* => *, F]

  def apply[->[_,_], F[_]](using E: Endofunctor[->, F]): Endofunctor[->, F] = E
  def unsafe[->[_,_], F[_]](fn: [a, b] => (a -> b) => (F[a] -> F[b])): Endofunctor[->, F] = Exofunctor.unsafe(fn)


type Endobifunctor[->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]
/** Endo bifunctor on scala function */
type EndobifunctorF[⊙[_,_]] = Endobifunctor[* => *, ⊙]
type Exoprofunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]] = Exobifunctor[Dual[==>,*,*], -->, >->, ⊙]
type Endoprofunctor[->[_,_], ⊙[_,_]] = Exobifunctor[Dual[->, *, *], ->, ->, ⊙]

type OplaxSemigroupal[=⊙[_, _], -->[_, _], -⊙[_, _], F[_]] = LaxSemigroupal[=⊙, Dual[-->, *, *], -⊙, F]
type OplaxMonoidal   [=⊙[_, _], -->[_, _], -⊙[_, _], F[_]] = LaxMonoidal   [=⊙, Dual[-->, *, *], -⊙, F]

type FunctorK[H[_[_]]] = Exo[FunK, * => *, HasTc[H, *]]
object FunctorK {
  def apply[H[_[_]]](implicit F: FunctorK[H]): FunctorK[H] = F
  trait Proto[H[_[_]]] extends FunctorK[H] {
    def map[A, B](f: FunK[A, B]): HasTc[H, A] => HasTc[H, B] = HasTc.isoFun(using f.kindA, f.kindB).flip(mapK(f.fn))
    protected def mapK[F[_], G[_]](f: F ~> G): H[F] => H[G]
  }
}

type CovariantK[H[_[_]]] = Exo[Dual[FunK,*,*], * => *, HasTc[H, *]]
object CofunctorK {
  def apply[H[_[_]]](implicit F: CovariantK[H]): CovariantK[H] = F
  trait Proto[H[_[_]]] extends CovariantK[H] {
    def map[A, B](f: Dual[FunK, A, B]): HasTc[H, A] => HasTc[H, B] = {
      val fn = f.toFn
      HasTc.isoFun[H, A, fn.TypeB, B, fn.TypeA](using fn.kindB, fn.kindA).flip(comapK(fn.fn))
    }
    protected def comapK[F[_], G[_]](f: G ~> F): H[F] => H[G]
  }
}

type IsoFunctorK[H[_[_]]] = Exo[IsoFunK, <=>, HasTc[H, *]]
object IsoFunctorK {
  def apply[H[_[_]]](implicit F: IsoFunctorK[H]): IsoFunctorK[H] = F

  trait Proto[H[_[_]]] extends IsoFunctorK[H] {
    def map[A, B](i: IsoFunK[A, B]): HasTc[H, A] <=> HasTc[H, B] = {
      val to = i.to
      val isok: to.TypeA <~> to.TypeB = FunK.isoFunKUnapply(i)(using to.kindA, to.kindB)
      Iso.unsafe(
        HasTc.isoFun(using to.kindA, to.kindB).flip(mapK(isok)),
        HasTc.isoFun(using to.kindB, to.kindA).flip(mapK(isok.flip))
      )
    }
    protected def mapK[F[_], G[_]](f: F <~> G): H[F] => H[G]
  }
}

