package io.cosmo.exo.functors

import io.cosmo.exo.categories.*
import io.cosmo.exo.*

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

type FunctorK[==>[_,_], -->[_,_], H[_[_]]] = Exo[ArrowK[==>,*,*], -->, HasTc[H, *]]
object FunctorK:
  def apply[==>[_,_], -->[_,_], H[_[_]]](using F: FunctorK[==>, -->, H]): FunctorK[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_]]] extends FunctorK[==>, -->, H]:
    def map[A, B](f: ArrowK[==>, A, B]): HasTc[H, A] --> HasTc[H, B] =
      val ia = HasTc.isoCanonic[H, A](using f.kindA)
      val ib = HasTc.isoCanonic[H, B](using f.kindB)
      bif.bimap(ia, ib)(mapK(f.fn))
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def mapK[F[_], G[_]](f: ∀[[a] =>> F[a] ==> G[a]]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_]]] extends FunctorK[==>, * => *, H]:
    def map[A, B](f: ArrowK[==>, A, B]): HasTc[H, A] => HasTc[H, B] =
      HasTc.isoFun(using f.kindA, f.kindB).to(mapK(f.fn))
    protected def mapK[F[_], G[_]](f: ∀[[a] =>> F[a] ==> G[a]]): H[F] => H[G]
  trait ProtoF[H[_[_]]] extends Proto1[* => *, H]

type CofunctorK[==>[_,_], -->[_,_], H[_[_]]] = Exo[Dual[ArrowK[==>,*,*],*,*], -->, HasTc[H, *]]
object CofunctorK:
  def apply[==>[_,_], -->[_,_], H[_[_]]](using F: CofunctorK[==>, -->, H]): CofunctorK[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_]]] extends CofunctorK[==>, -->, H]:
    def map[A, B](f: Dual[ArrowK[==>,*,*], A, B]): HasTc[H, A] --> HasTc[H, B] =
      val fn = f.toFn
      val ia = HasTc.isoCanonic[H, B](using fn.kindA)
      val ib = HasTc.isoCanonic[H, A](using fn.kindB)
      bif.bimap(ib, ia)(comapK(fn.fn))
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def comapK[F[_], G[_]](f: ∀[[a] =>> G[a] ==> F[a]]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_]]] extends CofunctorK[==>, * => *, H]:
    def map[A, B](f: Dual[ArrowK[==>,*,*], A, B]): HasTc[H, A] => HasTc[H, B] =
      val fn: ArrowK[==>, B, A] = f.toFn
      HasTc.isoFun[H, A, fn.TypeB, B, fn.TypeA](using fn.kindB, fn.kindA).to(comapK(fn.fn))
    protected def comapK[F[_], G[_]](f: G ~> F): H[F] => H[G]
  trait ProtoF[H[_[_]]] extends Proto1[* => *, H]

type IsoFunctorK[==>[_,_], -->[_,_], H[_[_]]] = Exo[IsoArrowK[==>,*,*], Iso[-->,*,*], HasTc[H, *]]
object IsoFunctorK:
  def apply[==>[_,_], -->[_,_], H[_[_]]](using F: IsoFunctorK[==>, -->, H]): IsoFunctorK[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_]]] extends IsoFunctorK[==>, -->, H]:
    def map[A, B](iso: IsoArrowK[==>, A, B]): Iso[-->, HasTc[H, A], HasTc[H, B]] =
      val to = iso.to
      val isok = ArrowK.isoFunKUnapply(iso)(using to.kindA, to.kindB)(using cat1)
      val iso1 = Iso.unsafe(mapK(isok), mapK(isok.flip))(using cat2)
      val ia = HasTc.isoCanonic[H, A](using to.kindA)
      val ib = HasTc.isoCanonic[H, B](using to.kindB)
      val x1 = bif.bimap(ia, ib)
      val x2 = bif.bimap(ib, ia)
      Iso.unsafe(x1(iso1.to), x2(iso1.from))(using iso1.cat)
    protected def cat1: Subcat[==>]
    protected def cat2: Subcat[-->]
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def mapK[F[_], G[_]](f: IsoK[==>, F, G]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_]]] extends IsoFunctorK[==>, * => *, H]:
    def map[A, B](f: IsoArrowK[==>, A, B]): Iso[* => *, HasTc[H, A], HasTc[H, B]] =
      val to = f.to
      val isok: IsoK[==>, to.TypeA, to.TypeB] = ArrowK.isoFunKUnapply(f)(using to.kindA, to.kindB)(using cat)
      Iso.unsafe(
        HasTc.isoFun(using to.kindA, to.kindB).to(mapK(isok)),
        HasTc.isoFun(using to.kindB, to.kindA).to(mapK(isok.flip))
      )
    protected def cat: Subcat[==>]
    protected def mapK[F[_], G[_]](f: IsoK[==>, F, G]): H[F] => H[G]
  trait ProtoF[H[_[_]]] extends Proto1[* => *, H]:
    protected def cat: Subcat[* => *] = summon

type FunctorK2[==>[_,_], -->[_,_], H[_[_,_]]] = Exo[ArrowK2[==>,*,*], -->, HasTc2[H, *]]
object FunctorK2:
  def apply[==>[_,_], -->[_,_], H[_[_,_]]](using F: FunctorK2[==>, -->, H]): FunctorK2[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_,_]]] extends FunctorK2[==>, -->, H]:
    def map[A, B](f: ArrowK2[==>, A, B]): HasTc2[H, A] --> HasTc2[H, B] =
      val ia = HasTc2.isoCanonic[H, A](using f.kindA)
      val ib = HasTc2.isoCanonic[H, B](using f.kindB)
      bif.bimap(ia, ib)(mapK2(f.fn))
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def mapK2[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] ==> G[a, b]]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_,_]]] extends FunctorK2[==>, * => *, H]:
    def map[A, B](f: ArrowK2[==>, A, B]): HasTc2[H, A] => HasTc2[H, B] =
      HasTc2.isoFun(using f.kindA, f.kindB).to(mapK2(f.fn))
    protected def mapK2[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] ==> G[a, b]]): H[F] => H[G]
  trait ProtoF[H[_[_,_]]] extends Proto1[* => *, H]

type CofunctorK2[==>[_,_], -->[_,_], H[_[_,_]]] = Exo[Dual[ArrowK2[==>,*,*],*,*], -->, HasTc2[H, *]]
object CofunctorK2:
  def apply[==>[_,_], -->[_,_], H[_[_,_]]](using F: CofunctorK2[==>, -->, H]): CofunctorK2[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_,_]]] extends CofunctorK2[==>, -->, H]:
    def map[A, B](f: Dual[ArrowK2[==>,*,*], A, B]): HasTc2[H, A] --> HasTc2[H, B] =
      val fn = f.toFn
      val ia = HasTc2.isoCanonic[H, B](using fn.kindA)
      val ib = HasTc2.isoCanonic[H, A](using fn.kindB)
      bif.bimap(ib, ia)(comapK2(fn.fn))
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def comapK2[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> G[a, b] ==> F[a, b]]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_,_]]] extends CofunctorK2[==>, * => *, H]:
    def map[A, B](f: Dual[ArrowK2[==>,*,*], A, B]): HasTc2[H, A] => HasTc2[H, B] =
      val fn: ArrowK2[==>, B, A] = f.toFn
      HasTc2.isoFun[H, A, fn.TypeB, B, fn.TypeA](using fn.kindB, fn.kindA).to(comapK2(fn.fn))
    protected def comapK2[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> G[a, b] ==> F[a, b]]): H[F] => H[G]
  trait ProtoF[H[_[_,_]]] extends Proto1[* => *, H]

type IsoFunctorK2[==>[_,_], -->[_,_], H[_[_,_]]] = Exo[IsoArrowK2[==>,*,*], Iso[-->,*,*], HasTc2[H, *]]
object IsoFunctorK2:
  def apply[==>[_,_], -->[_,_], H[_[_,_]]](using F: IsoFunctorK2[==>, -->, H]): IsoFunctorK2[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_,_]]] extends IsoFunctorK2[==>, -->, H]:
    def map[A, B](iso: IsoArrowK2[==>, A, B]): Iso[-->, HasTc2[H, A], HasTc2[H, B]] =
      val to = iso.to
      val isok = ArrowK2.isoFunK2Unapply(iso)(using to.kindA, to.kindB)(using cat1)
      val iso1 = Iso.unsafe(mapK2(isok), mapK2(isok.flip))(using cat2)
      val ia = HasTc2.isoCanonic[H, A](using to.kindA)
      val ib = HasTc2.isoCanonic[H, B](using to.kindB)
      val x1 = bif.bimap(ia, ib)
      val x2 = bif.bimap(ib, ia)
      Iso.unsafe(x1(iso1.to), x2(iso1.from))(using iso1.cat)
    protected def cat1: Subcat[==>]
    protected def cat2: Subcat[-->]
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def mapK2[F[_,_], G[_,_]](f: IsoK2[==>, F, G]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_,_]]] extends IsoFunctorK2[==>, * => *, H]:
    def map[A, B](f: IsoArrowK2[==>, A, B]): Iso[* => *, HasTc2[H, A], HasTc2[H, B]] =
      val to = f.to
      val isok: IsoK2[==>, to.TypeA, to.TypeB] = ArrowK2.isoFunK2Unapply(f)(using to.kindA, to.kindB)(using cat)
      Iso.unsafe(
        HasTc2.isoFun(using to.kindA, to.kindB).to(mapK2(isok)),
        HasTc2.isoFun(using to.kindB, to.kindA).to(mapK2(isok.flip))
      )
    protected def cat: Subcat[==>]
    protected def mapK2[F[_,_], G[_,_]](f: IsoK2[==>, F, G]): H[F] => H[G]
  trait ProtoF[H[_[_,_]]] extends Proto1[* => *, H]:
    protected def cat: Subcat[* => *] = summon

type FunctorH[==>[_,_], -->[_,_], H[_[_[_]]]] = Exo[ArrowH[==>,*,*], -->, HasHc[H, *]]
object FunctorH:
  def apply[==>[_,_], -->[_,_], H[_[_[_]]]](using F: FunctorH[==>, -->, H]): FunctorH[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_[_]]]] extends FunctorH[==>, -->, H]:
    def map[A, B](f: ArrowH[==>, A, B]): HasHc[H, A] --> HasHc[H, B] =
      val ia = HasHc.isoCanonic[H, A](using f.kindA)
      val ib = HasHc.isoCanonic[H, B](using f.kindB)
      bif.bimap(ia, ib)(mapH(f.fn))
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def mapH[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] ==> G[a]]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_[_]]]] extends FunctorH[==>, * => *, H]:
    def map[A, B](f: ArrowH[==>, A, B]): HasHc[H, A] => HasHc[H, B] =
      HasHc.isoFun(using f.kindA, f.kindB).to(mapH(f.fn))
    protected def mapH[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] ==> G[a]]): H[F] => H[G]
  trait ProtoF[H[_[_[_]]]] extends Proto1[* => *, H]

type CofunctorH[==>[_,_], -->[_,_], H[_[_[_]]]] = Exo[Dual[ArrowH[==>,*,*],*,*], -->, HasHc[H, *]]
object CofunctorH:
  def apply[==>[_,_], -->[_,_], H[_[_[_]]]](using F: CofunctorH[==>, -->, H]): CofunctorH[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_[_]]]] extends CofunctorH[==>, -->, H]:
    def map[A, B](f: Dual[ArrowH[==>,*,*], A, B]): HasHc[H, A] --> HasHc[H, B] =
      val fn = f.toFn
      val ia = HasHc.isoCanonic[H, B](using fn.kindA)
      val ib = HasHc.isoCanonic[H, A](using fn.kindB)
      bif.bimap(ib, ia)(comapH(fn.fn))
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def comapH[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> G[a] ==> F[a]]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_[_]]]] extends CofunctorH[==>, * => *, H]:
    def map[A, B](f: Dual[ArrowH[==>,*,*], A, B]): HasHc[H, A] => HasHc[H, B] =
      val fn: ArrowH[==>, B, A] = f.toFn
      HasHc.isoFun[H, A, fn.TypeB, B, fn.TypeA](using fn.kindB, fn.kindA).to(comapH(fn.fn))
    protected def comapH[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> G[a] ==> F[a]]): H[F] => H[G]
  trait ProtoF[H[_[_[_]]]] extends Proto1[* => *, H]

type IsoFunctorH[==>[_,_], -->[_,_], H[_[_[_]]]] = Exo[IsoArrowH[==>,*,*], Iso[-->,*,*], HasHc[H, *]]
object IsoFunctorH:
  def apply[==>[_,_], -->[_,_], H[_[_[_]]]](using F: IsoFunctorH[==>, -->, H]): IsoFunctorH[==>, -->, H] = F
  trait Proto[==>[_,_], -->[_,_], H[_[_[_]]]] extends IsoFunctorH[==>, -->, H]:
    def map[A, B](iso: IsoArrowH[==>, A, B]): Iso[-->, HasHc[H, A], HasHc[H, B]] =
      val to = iso.to
      val isok = ArrowH.isoFunKUnapply(iso)(using to.kindA, to.kindB)(using cat1)
      val iso1 = Iso.unsafe(mapH(isok), mapH(isok.flip))(using cat2)
      val ia = HasHc.isoCanonic[H, A](using to.kindA)
      val ib = HasHc.isoCanonic[H, B](using to.kindB)
      val x1 = bif.bimap(ia, ib)
      val x2 = bif.bimap(ib, ia)
      Iso.unsafe(x1(iso1.to), x2(iso1.from))(using iso1.cat)
    protected def cat1: Subcat[==>]
    protected def cat2: Subcat[-->]
    protected def bif: Exobifunctor[<=>, <=>, * => *, -->]
    protected def mapH[F[_[_]], G[_[_]]](f: IsoH[==>, F, G]): H[F] --> H[G]
  trait Proto1[==>[_,_], H[_[_[_]]]] extends IsoFunctorH[==>, * => *, H]:
    def map[A, B](f: IsoArrowH[==>, A, B]): Iso[* => *, HasHc[H, A], HasHc[H, B]] =
      val to = f.to
      val isok: IsoH[==>, to.TypeA, to.TypeB] = ArrowH.isoFunKUnapply(f)(using to.kindA, to.kindB)(using cat)
      Iso.unsafe(
        HasHc.isoFun(using to.kindA, to.kindB).to(mapH(isok)),
        HasHc.isoFun(using to.kindB, to.kindA).to(mapH(isok.flip))
      )
    protected def cat: Subcat[==>]
    protected def mapH[F[_[_]], G[_[_]]](f: IsoH[==>, F, G]): H[F] => H[G]
  trait ProtoF[H[_[_[_]]]] extends Proto1[* => *, H]:
    protected def cat: Subcat[* => *] = summon
