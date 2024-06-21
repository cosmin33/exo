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
end Endofunctor

type Endobifunctor[->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]
/** Endo bifunctor on scala function */
type EndobifunctorF[⊙[_,_]] = Endobifunctor[* => *, ⊙]
type Exoprofunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]] = Exobifunctor[Dual[==>,*,*], -->, >->, ⊙]
type Endoprofunctor[->[_,_], ⊙[_,_]] = Exobifunctor[Dual[->, *, *], ->, ->, ⊙]

type OplaxSemigroupal[=⊙[_, _], -->[_, _], -⊙[_, _], F[_]] = LaxSemigroupal[=⊙, Dual[-->, *, *], -⊙, F]
type OplaxMonoidal   [=⊙[_, _], -->[_, _], -⊙[_, _], F[_]] = LaxMonoidal   [=⊙, Dual[-->, *, *], -⊙, F]

type FunctorK[H[_[_]]] = Exo[FunK, * => *, HasTc[H, *]]
object FunctorK:
  def apply[H[_[_]]](implicit F: FunctorK[H]): FunctorK[H] = F

  trait Proto[H[_[_]]] extends FunctorK[H]:
    def map[A, B](f: FunK[A, B]): HasTc[H, A] => HasTc[H, B] = HasTc.isoFun(using f.kindA, f.kindB).flip(mapK(f.fn))
    protected def mapK[F[_], G[_]](f: F ~> G): H[F] => H[G]

end FunctorK

type CofunctorK[H[_[_]]] = Exo[Dual[FunK,*,*], * => *, HasTc[H, *]]
object CofunctorK:
  def apply[H[_[_]]](implicit F: CofunctorK[H]): CofunctorK[H] = F

  trait Proto[H[_[_]]] extends CofunctorK[H]:
    def map[A, B](f: Dual[FunK, A, B]): HasTc[H, A] => HasTc[H, B] =
      val fn = f.toFn
      HasTc.isoFun[H, A, fn.TypeB, B, fn.TypeA](using fn.kindB, fn.kindA).flip(comapK(fn.fn))
    protected def comapK[F[_], G[_]](f: G ~> F): H[F] => H[G]

end CofunctorK

type IsoFunctorK[H[_[_]]] = Exo[IsoFunK, <=>, HasTc[H, *]]
object IsoFunctorK:
  def apply[H[_[_]]](implicit F: IsoFunctorK[H]): IsoFunctorK[H] = F

  trait Proto[H[_[_]]] extends IsoFunctorK[H]:
    def map[A, B](i: IsoFunK[A, B]): HasTc[H, A] <=> HasTc[H, B] =
      val to = i.to
      val isok: to.TypeA <~> to.TypeB = FunK.isoFunKUnapply(i)(using to.kindA, to.kindB)
      Iso.unsafe(
        HasTc.isoFun(using to.kindA, to.kindB).flip(mapK(isok)),
        HasTc.isoFun(using to.kindB, to.kindA).flip(mapK(isok.flip))
      )
    protected def mapK[F[_], G[_]](f: F <~> G): H[F] => H[G]

end IsoFunctorK

type FunctorK2[H[_[_,_]]] = Exo[FunK2, * => *, HasTc2[H, *]]
object FunctorK2:
  def apply[H[_[_,_]]](implicit F: FunctorK2[H]): FunctorK2[H] = F

  trait Proto[H[_[_,_]]] extends FunctorK2[H]:
    def map[A, B](f: FunK2[A, B]): HasTc2[H, A] => HasTc2[H, B] = HasTc2.isoFun(using f.kindA, f.kindB).flip(mapK(f.fn))
    protected def mapK[F[_,_], G[_,_]](f: F ~~> G): H[F] => H[G]

end FunctorK2

type CofunctorK2[H[_[_,_]]] = Exo[Dual[FunK2,*,*], * => *, HasTc2[H, *]]
object CofunctorK2:
  def apply[H[_[_,_]]](implicit F: CofunctorK2[H]): CofunctorK2[H] = F

  trait Proto[H[_[_,_]]] extends CofunctorK2[H]:
    def map[A, B](f: Dual[FunK2, A, B]): HasTc2[H, A] => HasTc2[H, B] =
      val fn = f.toFn
      HasTc2.isoFun[H, A, fn.TypeB, B, fn.TypeA](using fn.kindB, fn.kindA).flip(comapK(fn.fn))
    protected def comapK[F[_,_], G[_,_]](f: G ~~> F): H[F] => H[G]

end CofunctorK2

type IsoFunctorK2[H[_[_,_]]] = Exo[IsoFunK2, <=>, HasTc2[H, *]]
object IsoFunctorK2:
  def apply[H[_[_,_]]](implicit F: IsoFunctorK2[H]): IsoFunctorK2[H] = F

  trait Proto[H[_[_,_]]] extends IsoFunctorK2[H]:
    def map[A, B](i: IsoFunK2[A, B]): HasTc2[H, A] <=> HasTc2[H, B] =
      val to = i.to
      val isok: to.TypeA <~~> to.TypeB = FunK2.isoFunK2Unapply(i)(using to.kindA, to.kindB)
      Iso.unsafe(
        HasTc2.isoFun(using to.kindA, to.kindB).flip(mapK(isok)),
        HasTc2.isoFun(using to.kindB, to.kindA).flip(mapK(isok.flip))
      )
    protected def mapK[F[_,_], G[_,_]](f: F <~~> G): H[F] => H[G]

end IsoFunctorK2

//type FunctorHK[H[_[_[_]]]] = Exo[FunHK, * => *, HasTcHK[H, *]]
//object FunctorHK:
//  def apply[H[_[_[_]]]](implicit F: FunctorHK[H]): FunctorHK[H] = F
//
//  trait Proto[H[_[_[_]]]] extends FunctorHK[H]:
//    def map[A, B](f: FunHK[A, B]): HasTcHK[H, A] => HasTcHK[H, B] = HasTcHK.isoFun(using f.kindA, f.kindB).flip(mapK(f.fn))
//    protected def mapK[F[_[_]], G[_[_]]](f: F ~> G): H[F] => H[G]
//
//end FunctorHK