package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax.*

trait ArrowH[->[_,_], A, B]:
  type TypeA[_[_]]
  type TypeB[_[_]]
  def kindA: IsHKind.Aux[A, TypeA]
  def kindB: IsHKind.Aux[B, TypeB]
  def fn: ∀~[[a[_]] =>> TypeA[a] -> TypeB[a]]
  def unapply(using ia: IsHKind[A], ib: IsHKind[B]): ∀~[[a[_]] =>> ia.Type[a] -> ib.Type[a]] =
    IsHK.lower2[[F[_[_]], G[_[_]]] =>> ∀~[[a[_]] =>> F[a] -> G[a]], TypeA, ia.Type, TypeB, ib.Type](
      IsHKind.injectivity(kindA, ia),
      IsHKind.injectivity(kindB, ib)
    )(fn)
    
object ArrowH extends ArrowHImplicits {
  type Aux[->[_,_], A, B, F[_[_]], G[_[_]]] = ArrowH[->, A, B] { type TypeA[x[_]] = F[x]; type TypeB[x[_]] = G[x] }
  def apply[->[_,_], A, B, F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]])(
    using a: IsHKind.Aux[A, F], b: IsHKind.Aux[B, G]
  ): ArrowH.Aux[->, A, B, F, G] =
    new ArrowH[->, A, B] { type TypeA[x[_]] = F[x]; type TypeB[x[_]] = G[x]; val (kindA, kindB, fn) = (a, b, f) }
    
  def from[->[_,_], A, B](using ia: IsHKind[A], ib: IsHKind[B]): MkArrowHK[->, A, B, ia.Type, ib.Type] =
    new MkArrowHK[->, A, B, ia.Type, ib.Type](ia, ib)
  case class MkArrowHK[->[_,_], A, B, F[_[_]], G[_[_]]](ia: IsHKind.Aux[A, F], ib: IsHKind.Aux[B, G]):
    def apply(f: ∀~[[a[_]] =>> F[a] -> G[a]]): ArrowH.Aux[->, A, B, F, G] = ArrowH.apply[->, A, B, F, G](f)(using ia, ib)

  def isoFunKUnapply[->[_,_], A, B](i: Iso[ArrowH[->,*,*], A, B])(
    using a: IsHKind[A], b: IsHKind[B])(
    using s: Subcat[->]
  ): IsoHK[->, a.Type, b.Type] = IsoHK.unsafe(i.to.unapply, i.from.unapply)

  def isInjective[->[_,_]]: IsInjective2[ArrowH[->,*,*]] = IsInjective2.witness1[ArrowH[->,*,*], 1, 2, 3]

  given invertDual[->[_,_]]: (ArrowH[Dual[->,*,*],*,*] <~~> Dual[ArrowH[->,*,*],*,*]) =
    <~~>.unsafe([A, B] => () =>
      <=>.unsafe[ArrowH[Dual[->,*,*],A,B], Dual[ArrowH[->,*,*],A,B]](
        ad => Dual(ArrowH.from(using ad.kindB, ad.kindA)(∀~.of.fromH([a[_]] => () => ad.fn[a].toFn))),
        da => ArrowH.from(using da.kindB, da.kindA)(∀~.of.fromH([a[_]] => () => Dual(da.fn[a])))
      )
    )

  given isoArrowHCanonic[->[_,_], A, B](using a: IsHKind[A], b: IsHKind[B])
  : (ArrowH[->, A, B] <=> ∀~[[a[_]] =>> a.Type[a] -> b.Type[a]]) =
    Iso.unsafe(_.unapply, apply)

  given isoIsoArrowHCanonic[->[_,_], A, B](using a: IsHKind[A], b: IsHKind[B])(using s: Subcat.Aux[->, Trivial])
  : (Iso[ArrowH[->,*,*], A, B] <=> IsoHK[->, a.Type, b.Type]) =
    Iso.unsafe(i => IsoHK.unsafe(i.to.unapply, i.from.unapply), i => Iso.unsafe(apply(i.to), apply(i.from)))

}

import ArrowHKHelpers.*

trait ArrowHImplicits extends ArrowHImplicits01 {
  given bifunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]](using b: Exobifunctor[==>, -->, >->, ⊙], i: IsInjective2[⊙])
  : Exobifunctor[ArrowH[==>,*,*], ArrowH[-->,*,*], ArrowH[>->,*,*], ⊙] =
    new BifunctorArrowH[==>, -->, >->, ⊙] { val (bif, inj) = (b, i) }
  given distributive[->[_,_], ⨂[_,_], ProductId, ⨁[_,_], SumId](using
    s: Distributive.Aux[->, Trivial, ⨂, ProductId, ⨁, SumId], ip: IsInjective2[⨂], is: IsInjective2[⨁]
  ): Distributive.Aux[ArrowH[->,*,*], IsHKind, ⨂, TypeHK[[a[_]] =>> ProductId], ⨁, TypeHK[[a[_]] =>> SumId]] =
    new DistributiveArrowH[->, ⨂, ProductId, ⨁, SumId] { val (cat, injP, injS) = (s, ip, is) }
  given ccc[->[_,_], ⊙[_,_], I, E[_,_]](using c: Ccc.Aux[->, ⊙, E, Trivial, I], ip: IsInjective2[⊙], ie: IsInjective2[E])
  : Ccc.Aux[ArrowH[->,*,*], ⊙, E, IsHKind, TypeHK[[a[_]] =>> I]] =
    new CccArrowH[->, ⊙, I, E] { val (assoc, inj, injE) = (c, ip, ie) }
  given ccc1[->[_,_], ⊙[_,_], I](using c: Ccc.Aux[->, ⊙, ->, Trivial, I], i: IsInjective2[⊙], ie: IsInjective2[->])
  : Ccc.Aux[ArrowH[->,*,*], ⊙, ArrowH[->,*,*], IsHKind, TypeHK[[a[_]] =>> I]] =
    new Ccc1ArrowH[->, ⊙, I] { val (assoc, inj, injE) = (c, i, ie) }
  given initial[->[_,_], I](using i: Initial.Aux[->, Trivial, I]): Initial.Aux[ArrowH[->,*,*], IsHKind, TypeHK[[a[_]] =>> I]] =
    new InitialArrowH[->, I] { val ini = i }
  given terminal[->[_,_], T](using t: Terminal.Aux[->, Trivial, T]): Terminal.Aux[ArrowH[->,*,*], IsHKind, TypeHK[[a[_]] =>> T]] =
    new TerminalArrowH[->, T] { val term = t }
}

trait ArrowHImplicits01 extends ArrowHImplicits02 {
  given subcat[->[_,_]](using s: Subcat.Aux[->, Trivial]): Subcat.Aux[ArrowH[->,*,*], IsHKind] =
    new SubcatArrowH[->] { val cat = s }
  given cartesian[->[_,_], ⊙[_,_], I](using c: Cartesian.Aux[->, ⊙, Trivial, I], i: IsInjective2[⊙])
  : Cartesian.Aux[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]] =
    new CartesianArrowH[->, ⊙, I] { val (assoc, inj) = (c, i) }
  given coCartesian[->[_,_], ⊙[_,_], I](using c: Cartesian.Aux[Dual[->,*,*], ⊙, Trivial, I], i: IsInjective2[⊙])
  : Cartesian.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]] =
    new CoCartesianArrowH[->, ⊙, I] { val (assoc, inj) = (c, i) }
}

trait ArrowHImplicits02 extends ArrowHImplicits03 {
  given semicat[->[_,_]](using s: Semicategory[->]): Semicategory[ArrowH[->,*,*]] =
    new SemicategoryArrowH[->] { val cat = s }
  given monoidal[->[_,_], ⊙[_,_], I](using m: Monoidal.Aux[->, ⊙, Trivial, I], i: IsInjective2[⊙])
  : Monoidal.Aux[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]] =
    new MonoidalArrowH[->, ⊙, I] { val (assoc, inj) = (m, i) }
  given coMonoidal[->[_,_], ⊙[_,_], I](using m: Monoidal.Aux[Dual[->,*,*], ⊙, Trivial, I], i: IsInjective2[⊙])
  : Monoidal.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]] =
    new CoMonoidalArrowH[->, ⊙, I] { val (assoc, inj) = (m, i) }
}

trait ArrowHImplicits03 extends ArrowHImplicits04 {
  given symmetric[->[_,_], ⊙[_,_]](using a: Symmetric.Aux[->, ⊙, Trivial], i: IsInjective2[⊙])
  : Symmetric.Aux[ArrowH[->,*,*], ⊙, IsHKind] =
    new BraidedArrowH[->, ⊙] with Symmetric[ArrowH[->,*,*], ⊙] { val (assoc, inj) = (a, i) }
  given coSymmetric[->[_,_], ⊙[_,_]](using a: Symmetric.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙])
  : Symmetric.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind] =
    new CoBraidedArrowH[->, ⊙] with Symmetric[Dual[ArrowH[->,*,*],*,*], ⊙] { val (assoc, inj)  = (a, i) }
}

trait ArrowHImplicits04 extends ArrowHImplicits05 {
  given braided[->[_,_], ⊙[_,_]](using a: Braided.Aux[->, ⊙, Trivial], i: IsInjective2[⊙]): Braided.Aux[ArrowH[->,*,*], ⊙, IsHKind] =
    new BraidedArrowH[->, ⊙] { val (assoc, inj) = (a, i) }
  given coBraided[->[_,_], ⊙[_,_]](using a: Braided.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙]): Braided.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind] =
    new CoBraidedArrowH[->, ⊙] { val (assoc, inj) = (a, i) }
}

trait ArrowHImplicits05 {
  given associative[->[_,_], ⊙[_,_]](using a: Associative.Aux[->, ⊙, Trivial], i: IsInjective2[⊙]): Associative[ArrowH[->,*,*], ⊙] =
    new AssociativeArrowH[->, ⊙] { val (assoc, inj) = (a, i) }
  given coAssociative[->[_,_], ⊙[_,_]](using a: Associative.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙]): Associative[Dual[ArrowH[->,*,*],*,*], ⊙] =
    new CoAssociativeArrowH[->, ⊙] { val (assoc, inj) = (a, i) }
}

object ArrowHKHelpers:
  trait BifunctorArrowH[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]]
    extends Exobifunctor[ArrowH[==>,*,*], ArrowH[-->,*,*], ArrowH[>->,*,*], ⊙]:
    protected def bif: Exobifunctor[==>, -->, >->, ⊙]
    protected given inj: IsInjective2[⊙]
    def bimap[A, X, B, Y](l: ArrowH[==>, A, X], r: ArrowH[-->, B, Y]): ArrowH[>->, A ⊙ B, X ⊙ Y] =
      ArrowH.from[>->, A ⊙ B, X ⊙ Y](using
        IsHKind.pairInjectivity[⊙, A, B](using l.kindA, r.kindA),
        IsHKind.pairInjectivity[⊙, X, Y](using l.kindB, r.kindB)
      )(∀~.of.fromH([a[_]] => () => bif.bimap(l.fn[a], r.fn[a])))


  trait SemicategoryArrowH[->[_,_]] extends Semicategory[ArrowH[->,*,*]]:
    protected def cat: Semicategory[->]
    def andThen[A, B, C](ab: ArrowH[->, A, B], bc: ArrowH[->, B, C]): ArrowH[->, A, C] =
      val fa: ∀~[[a[_]] =>> ab.TypeB[a] -> bc.TypeB[a]] =
        IsHKind.injectivity(ab.kindB, bc.kindA).flip.subst[[f[_[_]]] =>> ∀~[[a[_]] =>> f[a] -> bc.TypeB[a]]](bc.fn)
      ArrowH.from[->, A, C](using ab.kindA, bc.kindB)(∀~.of.fromH([a[_]] => () => cat.andThen(ab.fn[a], fa[a])))

  trait SubcatArrowH[->[_,_]] extends SemicategoryArrowH[->] with Subcat.Proto[ArrowH[->,*,*], IsHKind]:
    override def cat: Subcat.Aux[->, Trivial]
    def id[A](using A: IsHKind[A]): ArrowH[->, A, A] =
      ArrowH(∀~.from(new ∀~.Prototype[[a[_]] =>> A.Type[a] -> A.Type[a]] { def apply[a[_]] = cat.id[A.Type[a]] }))

  trait DistributiveArrowH[->[_,_], ⨂[_,_], ProductId, ⨁[_,_], SumId]
    extends SubcatArrowH[->]
      with Distributive.Proto[ArrowH[->,*,*], IsHKind, ⨂, TypeHK[[a[_]] =>> ProductId], ⨁, TypeHK[[a[_]] =>> SumId]]:
    override def cat: Distributive.Aux[->, Trivial, ⨂, ProductId, ⨁, SumId]
    given injP: IsInjective2[⨂]
    given injS: IsInjective2[⨁]
    given Cartesian.Aux[->, ⨂, Trivial, ProductId] = cat.cartesian
    given Cocartesian.Aux[->, ⨁, Trivial, SumId] = cat.cocartesian
    def cartesian: Cartesian.Aux[ArrowH[->,*,*], ⨂, IsHKind, TypeHK[[a[_]] =>> ProductId]] = summon
    def cocartesian: Cocartesian.Aux[ArrowH[->,*,*], ⨁, IsHKind, TypeHK[[a[_]] =>> SumId]] = summon
    def distribute[A, B, C](using ia: IsHKind[A], ib: IsHKind[B], ic: IsHKind[C]): ArrowH[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]] =
      ArrowH.from[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]](
        ∀~.of.fromH([a[_]] => () => cat.distribute[ia.Type[a], ib.Type[a], ic.Type[a]])
      )

  trait AssociativeArrowH[->[_,_], ⊙[_,_]] extends Associative[ArrowH[->,*,*], ⊙]:
    type TC[a] = IsHKind[a]
    protected def assoc: Associative.Aux[->, ⊙, Trivial]
    private given Endobifunctor[->, ⊙] = assoc.bifunctor
    private given Subcat.Aux[->, Trivial] = assoc.C
    protected given inj: IsInjective2[⊙]
    def C: Subcat.Aux[ArrowH[->,*,*], IsHKind] = summon
    def bifunctor: Endobifunctor[ArrowH[->,*,*], ⊙] = summon
    def associate  [A, B, C](using ia: IsHKind[A], ib: IsHKind[B], ic: IsHKind[C]): ArrowH[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]] =
      ArrowH.from[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]](
        ∀~.of.fromH([a[_]] => () => assoc.associate[ia.Type[a], ib.Type[a], ic.Type[a]])
      )
    def diassociate[A, B, C](using ia: IsHKind[A], ib: IsHKind[B], ic: IsHKind[C]): ArrowH[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]] =
      ArrowH.from[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]](
        ∀~.of.fromH([a[_]] => () => assoc.diassociate[ia.Type[a], ib.Type[a], ic.Type[a]])
      )

  trait CoAssociativeArrowH[->[_,_], ⊙[_,_]] extends Associative[Dual[ArrowH[->,*,*],*,*], ⊙]:
    type TC[a] = IsHKind[a]
    protected def assoc: Associative.Aux[Dual[->,*,*], ⊙, Trivial]
    private given Endobifunctor[Dual[->,*,*], ⊙] = assoc.bifunctor
    private given Subcat.Aux[Dual[->,*,*], Trivial] = assoc.C
    protected given inj: IsInjective2[⊙]
    def C: Subcat.Aux[[a,b] =>> Dual[ArrowH[->,*,*],a,b], IsHKind] = summon
    def bifunctor: Endobifunctor[[a,b] =>> Dual[ArrowH[->,*,*],a,b], ⊙] =
      val ff = Endobifunctor[ArrowH[Dual[->,*,*],*,*], ⊙]
      IsoFunctorK2[[f[_,_]] =>> Endobifunctor[f, ⊙]].isoMapK2(ArrowH.invertDual)(ff)
    def associate[A, B, C](using ia: IsHKind[A], ib: IsHKind[B], ic: IsHKind[C]): Dual[ArrowH[->,*,*], A ⊙ B ⊙ C, A ⊙ (B ⊙ C)] =
      Dual(ArrowH.from[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]](
        ∀~.of.fromH([a[_]] => () => assoc.associate[ia.Type[a], ib.Type[a], ic.Type[a]])
      ))
    def diassociate[A, B, C](using ia: IsHKind[A], ib: IsHKind[B], ic: IsHKind[C]): Dual[ArrowH[->,*,*], A ⊙ (B ⊙ C), A ⊙ B ⊙ C] =
      Dual(ArrowH.from[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]](
        ∀~.of.fromH([a[_]] => () => assoc.diassociate[ia.Type[a], ib.Type[a], ic.Type[a]])
      ))

  trait BraidedArrowH[->[_,_], ⊙[_,_]] extends AssociativeArrowH[->, ⊙] with Braided.Proto[ArrowH[->,*,*], ⊙, IsHKind]:
    protected def assoc: Braided.Aux[->, ⊙, Trivial]
    def braid[A, B](using ia: IsHKind[A], ib: IsHKind[B]): ArrowH[->, A ⊙ B, B ⊙ A] =
      ArrowH.from[->, A ⊙ B, B ⊙ A](∀~.of.fromH([a[_]] => () => assoc.braid[ia.Type[a], ib.Type[a]]))

  trait CoBraidedArrowH[->[_,_], ⊙[_,_]]
    extends CoAssociativeArrowH[->, ⊙]
      with Braided.Proto[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind]:
    protected def assoc: Braided.Aux[Dual[->,*,*], ⊙, Trivial]
    def braid[A, B](using ia: IsHKind[A], ib: IsHKind[B]): Dual[ArrowH[->,*,*], A ⊙ B, B ⊙ A] =
      Dual(ArrowH.from[->, B ⊙ A, A ⊙ B](∀~.of.fromH([a[_]] => () => assoc.braid[ia.Type[a], ib.Type[a]])))

  trait MonoidalArrowH[->[_,_], ⊙[_,_], I]
    extends AssociativeArrowH[->, ⊙]
      with Monoidal.Proto[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]]:
    protected def assoc: Monoidal.Aux[->, ⊙, Trivial, I]
    def idl[A](using a: IsHKind[A]): ArrowH[->, Id ⊙ A, A] =
      ArrowH.from[->, Id ⊙ A, A](∀~.of.fromH([a[_]] => () => assoc.idl[a.Type[a]]))
    def coidl[A](using a: IsHKind[A]): ArrowH[->, A, Id ⊙ A] =
      ArrowH.from[->, A, Id ⊙ A](∀~.of.fromH([a[_]] => () => assoc.coidl[a.Type[a]]))
    def idr[A](using a: IsHKind[A]): ArrowH[->, A ⊙ Id, A] =
      ArrowH.from[->, A ⊙ Id, A](∀~.of.fromH([a[_]] => () => assoc.idr[a.Type[a]]))
    def coidr[A](using a: IsHKind[A]): ArrowH[->, A, A ⊙ Id] =
      ArrowH.from[->, A, A ⊙ Id](∀~.of.fromH([a[_]] => () => assoc.coidr[a.Type[a]]))

  trait CoMonoidalArrowH[->[_,_], ⊙[_,_], I]
    extends CoAssociativeArrowH[->, ⊙]
      with Monoidal.Proto[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]]:
    protected def assoc: Monoidal.Aux[Dual[->,*,*], ⊙, Trivial, I]
    def idl[A](using a: IsHKind[A]): Dual[ArrowH[->,*,*], Id ⊙ A, A] =
      Dual(ArrowH.from[->, A, Id ⊙ A](∀~.of.fromH([a[_]] => () => assoc.idl[a.Type[a]].toFn)))
    def coidl[A](using a: IsHKind[A]): Dual[ArrowH[->,*,*], A, Id ⊙ A] =
      Dual(ArrowH.from[->, Id ⊙ A, A](∀~.of.fromH([a[_]] => () => assoc.coidl[a.Type[a]].toFn)))
    def idr[A](using a: IsHKind[A]): Dual[ArrowH[->,*,*], A ⊙ Id, A] =
      Dual(ArrowH.from[->, A, A ⊙ Id](∀~.of.fromH([a[_]] => () => assoc.idr[a.Type[a]].toFn)))
    def coidr[A](using a: IsHKind[A]): Dual[ArrowH[->,*,*], A, A ⊙ Id] =
      Dual(ArrowH.from[->, A ⊙ Id, A](∀~.of.fromH([a[_]] => () => assoc.coidr[a.Type[a]].toFn)))

  trait CartesianArrowH[->[_,_], ⊙[_,_], I]
    extends MonoidalArrowH[->, ⊙, I]
      with BraidedArrowH[->, ⊙]
      with Cartesian.Proto[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]]:
    protected def assoc: Cartesian.Aux[->, ⊙, Trivial, I]
    def fst[A, B](using a: IsHKind[A], b: IsHKind[B]): ArrowH[->, A ⊙ B, A] =
      ArrowH.from[->, A ⊙ B, A](∀~.of.fromH([a[_]] => () => assoc.fst[a.Type[a], b.Type[a]]))
    def snd[A, B](using a: IsHKind[A], b: IsHKind[B]): ArrowH[->, A ⊙ B, B] =
      ArrowH.from[->, A ⊙ B, B](∀~.of.fromH([a[_]] => () => assoc.snd[a.Type[a], b.Type[a]]))
    def diag[A](using a: IsHKind[A]): ArrowH[->, A, A ⊙ A] =
      ArrowH.from[->, A, A ⊙ A](∀~.of.fromH([a[_]] => () => assoc.diag[a.Type[a]]))
    def &&&[A, B, C](f: ArrowH[->, A, B], g: ArrowH[->, A, C]): ArrowH[->, A, B ⊙ C] =
      given ia: IsHKind.Aux[A, f.TypeA] = f.kindA
      given ib: IsHKind.Aux[B, f.TypeB] = f.kindB
      given ic: IsHKind.Aux[C, g.TypeB] = g.kindB
      ArrowH.from[->, A, B ⊙ C](
        ∀~.of.fromH([a[_]] => () => assoc.merge[ia.Type[a], ib.Type[a], ic.Type[a]](f.unapply[a], g.unapply[a]))
      )

  trait CoCartesianArrowH[->[_,_], ⊙[_,_], I]
    extends CoMonoidalArrowH[->, ⊙, I]
      with CoBraidedArrowH[->, ⊙]
      with Cartesian.Proto[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> I]]:
    protected def assoc: Cartesian.Aux[Dual[->,*,*], ⊙, Trivial, I]
    def fst[A, B](using a: IsHKind[A], b: IsHKind[B]): Dual[ArrowH[->,*,*], A ⊙ B, A] =
      Dual(ArrowH.from[->, A, A ⊙ B](∀~.of.fromH([a[_]] => () => assoc.fst[a.Type[a], b.Type[a]])))
    def snd[A, B](using a: IsHKind[A], b: IsHKind[B]): Dual[ArrowH[->,*,*], A ⊙ B, B] =
      Dual(ArrowH.from[->, B, A ⊙ B](∀~.of.fromH([a[_]] => () => assoc.snd[a.Type[a], b.Type[a]])))
    def diag[A](using a: IsHKind[A]): Dual[ArrowH[->,*,*], A, A ⊙ A] =
      Dual(ArrowH.from[->, A ⊙ A, A](∀~.of.fromH([a[_]] => () => assoc.diag[a.Type[a]])))
    def &&&[A, B, C](f: Dual[ArrowH[->,*,*], A, B], g: Dual[ArrowH[->,*,*], A, C]): Dual[ArrowH[->,*,*], A, B ⊙ C] =
      given ia: IsHKind[A] = f.toFn.kindB
      given ib: IsHKind[B] = f.toFn.kindA
      given ic: IsHKind[C] = g.toFn.kindA
      Dual(ArrowH.from[->, B ⊙ C, A](
        ∀~.of.fromH([a[_]] => () => assoc.&&&[ia.Type[a], ib.Type[a], ic.Type[a]](Dual(f.toFn.unapply[a]), Dual(g.toFn.unapply[a])))
      ))

  trait InitialArrowH[->[_,_], I0] extends Initial[ArrowH[->,*,*]]:
    type TC[a] = IsHKind[a]
    type I = TypeHK[[x[_]] =>> I0]
    protected def ini: Initial.Aux[->, Trivial, I0]
    def TC: IsHKind[I] = summon
    def subcat: Subcat.Aux[ArrowH[->,*,*], IsHKind] = ArrowH.subcat[->](using ini.subcat)
    def initiate[A](using a: IsHKind[A]): ArrowH[->, I, A] =
      ArrowH.from[->, I, A](∀~.of.fromH([a[_]] => () => ini.initiate[a.Type[a]]))

  trait TerminalArrowH[->[_,_], T] extends Initial[[a,b] =>> Dual[ArrowH[->,*,*], a, b]] {
    type TC[a] = IsHKind[a]
    type I = TypeHK[[a[_]] =>> T]
    protected def term: Terminal.Aux[->, Trivial, T]
    def TC: IsHKind[I] = summon
    def subcat: Subcat.Aux[Dual[ArrowH[->,*,*],*,*], IsHKind] =
      val sad = ArrowH.subcat[Dual[->,*,*]](using term.subcat)
      IsoFunctorK2[[f[_,_]] =>> Subcat.Aux[f, IsHKind]].isoMapK2(ArrowH.invertDual)(sad)
    def initiate[A](using A: IsHKind[A]): Dual[ArrowH[->,*,*], TypeHK[[a[_]] =>> T], A] =
      Dual(ArrowH.from[->, A, TypeHK[[a[_]] =>> T]](∀~.of.fromH([a[_]] => () => term.terminate[A.Type[a]])))
  }

  trait CccArrowH[->[_,_], ⊙[_,_], PI, E[_,_]]
    extends CartesianArrowH[->, ⊙, PI]
      with Ccc.Proto[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> PI], E]:
    protected def assoc: Ccc.Aux[->, ⊙, E, Trivial, PI]
    protected given injE: IsInjective2[E]
    def curry[A, B, C](f: ArrowH[->, A ⊙ B, C]): ArrowH[->, A, E[B, C]] =
      val (ta: IsHKind[A], tb: IsHKind[B]) = f.kindA.pairInjectivity[⊙, A, B]
      given IsHKind.Aux[A, ta.Type] = ta
      given IsHKind.Aux[B, tb.Type] = tb
      given IsHKind.Aux[C, f.TypeB] = f.kindB
      ArrowH.from[->, A, E[B, C]](∀~.of.fromH([a[_]] => () => assoc.curry[ta.Type[a], tb.Type[a], f.TypeB[a]](f.unapply[a])))
    def uncurry[A, B, C](f: ArrowH[->, A, E[B, C]]): ArrowH[->, A ⊙ B, C] =
      val (tb: IsHKind[B], tc: IsHKind[C]) = f.kindB.pairInjectivity[E, B, C]
      given IsHKind.Aux[A, f.TypeA] = f.kindA
      given IsHKind.Aux[B, tb.Type] = tb
      given IsHKind.Aux[C, tc.Type] = tc
      ArrowH.from[->, A ⊙ B, C](∀~.of.fromH([a[_]] => () => assoc.uncurry[f.TypeA[a], tb.Type[a], tc.Type[a]](f.unapply[a])))

  trait Ccc1ArrowH[->[_,_], ⊙[_,_], PI]
    extends CartesianArrowH[->, ⊙, PI]
      with Ccc.Proto[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[[a[_]] =>> PI], ArrowH[->,*,*]]:
    protected def assoc: Ccc.Aux[->, ⊙, ->, Trivial, PI]
    protected given injE: IsInjective2[->]
    def curry[A, B, C](f: ArrowH[->, A ⊙ B, C]): ArrowH[->, A, ArrowH[->, B, C]] =
      val (ta: IsHKind[A], tb: IsHKind[B]) = f.kindA.pairInjectivity[⊙, A, B]
      given IsHKind.Aux[A, ta.Type] = ta
      given IsHKind.Aux[B, tb.Type] = tb
      given IsHKind.Aux[C, f.TypeB] = f.kindB
      ArrowH.from[->, A, ArrowH[->, B, C]](
        ∀~.of.fromH([a[_]] => () => assoc.curry[ta.Type[a], tb.Type[a], f.TypeB[a]](f.unapply[a]))
      )
    def uncurry[A, B, C](f: ArrowH[->, A, ArrowH[->, B, C]]): ArrowH[->, A ⊙ B, C] =
      given IsInjective2[ArrowH[->,*,*]] = ArrowH.isInjective[->]
      val (tb: IsHKind[B], tc: IsHKind[C]) = f.kindB.pairInjectivity[ArrowH[->,*,*], B, C]
      given IsHKind.Aux[A, f.TypeA] = f.kindA
      given IsHKind.Aux[B, tb.Type] = tb
      given IsHKind.Aux[C, tc.Type] = tc
      ArrowH.from[->, A ⊙ B, C](
        ∀~.of.fromH([a[_]] => () => assoc.uncurry[f.TypeA[a], tb.Type[a], tc.Type[a]](f.unapply[a]))
      )

end ArrowHKHelpers
