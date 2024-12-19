package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax.*

trait ArrowK2[->[_,_], A, B]:
  type TypeA[_,_]
  type TypeB[_,_]
  def kindA: IsKind2.Aux[A, TypeA]
  def kindB: IsKind2.Aux[B, TypeB]
  def fn: ∀∀[[x, y] =>> TypeA[x, y] -> TypeB[x, y]]
  def unapply(using ia: IsKind2[A], ib: IsKind2[B]): ∀∀[[a,b] =>> ia.Type[a,b] -> ib.Type[a,b]] =
    IsK2.lower2[[F[_,_], G[_,_]] =>> ∀∀[[a, b] =>> F[a,b] -> G[a,b]]].on[TypeA, ia.Type, TypeB, ib.Type](
      IsKind2.injectivity(kindA, ia),
      IsKind2.injectivity(kindB, ib)
    )(fn)

object ArrowK2 extends ArrowK2Implicits {
  type Aux[->[_,_], A, B, F[_,_], G[_,_]] = ArrowK2[->, A, B] { type TypeA[a, b] = F[a, b]; type TypeB[a, b] = G[a, b] }
  def apply[->[_,_], A, B, F[_,_], G[_,_]](f: ∀∀[[x, y] =>> F[x, y] -> G[x, y]])(
    using ia: IsKind2.Aux[A, F], ib: IsKind2.Aux[B, G]
  ): ArrowK2[->, A, B] =
    new ArrowK2[->, A, B] { type TypeA[a, b] = F[a, b]; type TypeB[a, b] = G[a, b]; val (kindA, kindB, fn) = (ia, ib, f) }
  
  def from[->[_,_], A, B](using ia: IsKind2[A], ib: IsKind2[B]): MkArrowK2[->, A, B, ia.Type, ib.Type] =
    new MkArrowK2[->, A, B, ia.Type, ib.Type](ia, ib)
  case class MkArrowK2[->[_,_], A, B, F[_,_], G[_,_]](ia: IsKind2.Aux[A, F], ib: IsKind2.Aux[B, G]):
    def apply(f: ∀∀[[x, y] =>> ia.Type[x, y] -> ib.Type[x, y]]): ArrowK2[->, A, B] = ArrowK2.apply[->, A, B, F, G](f)(using ia, ib)

  def isoFunK2Unapply[->[_,_], A, B](i: Iso[ArrowK2[->,*,*], A, B])(
    using a: IsKind2[A], b: IsKind2[B])(
    using s: Subcat[->]
  ): IsoK2[->, a.Type, b.Type] = IsoK2.unsafe(i.to.unapply, i.from.unapply)

  def isInjective[->[_,_]]: IsInjective2[ArrowK2[->,*,*]] = IsInjective2.witness1[ArrowK2[->,*,*], 1, 2, 3]

  given invertDual[->[_,_]]: (ArrowK2[Dual[->,*,*],*,*] <~~> Dual[ArrowK2[->,*,*],*,*]) =
    <~~>.unsafe([A, B] => () =>
      <=>.unsafe[ArrowK2[Dual[->,*,*],A,B], Dual[ArrowK2[->,*,*],A,B]](
        ad => Dual(ArrowK2.from(using ad.kindB, ad.kindA)(∀∀.of.fromH([a,b] => () => ad.fn[a,b].toFn))),
        da => ArrowK2.from(using da.kindB, da.kindA)(∀∀.of.fromH([a,b] => () => Dual(da.fn[a,b])))
      )
    )

  given isoArrowK2Canonic[->[_,_], A, B](using a: IsKind2[A], b: IsKind2[B])
  : (ArrowK2[->, A, B] <=> ∀∀[[a,b] =>> a.Type[a,b] -> b.Type[a,b]]) =
    Iso.unsafe(_.unapply, apply)

  given isoIsoArrowK2Canonic[->[_,_], A, B](using a: IsKind2[A], b: IsKind2[B])(using s: Subcat.Aux[->, Trivial])
  : (Iso[ArrowK2[->,*,*], A, B] <=> IsoK2[->, a.Type, b.Type]) =
    Iso.unsafe(i => IsoK2.unsafe(i.to.unapply, i.from.unapply), i => Iso.unsafe(apply(i.to), apply(i.from)))

}

import ArrowK2Helpers.*

trait ArrowK2Implicits extends ArrowK2Implicits01 {
  given bifunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]](using b: Exobifunctor[==>, -->, >->, ⊙], i: IsInjective2[⊙])
  : Exobifunctor[ArrowK2[==>,*,*], ArrowK2[-->,*,*], ArrowK2[>->,*,*], ⊙] =
    new BifunctorArrowK2[==>, -->, >->, ⊙] { val (bif, inj) = (b, i) }
  given distributive[->[_,_], ⨂[_,_], ProductId, ⨁[_,_], SumId](using
    s: Distributive.Aux[->, Trivial, ⨂, ProductId, ⨁, SumId], ip: IsInjective2[⨂], is: IsInjective2[⨁]
  ): Distributive.Aux[ArrowK2[->,*,*], IsKind2, ⨂, TypeK2[[a,b] =>> ProductId], ⨁, TypeK2[[a,b] =>> SumId]] =
    new DistributiveArrowK2[->, ⨂, ProductId, ⨁, SumId] { val (cat, injP, injS) = (s, ip, is) }
  given ccc[->[_,_], ⊙[_,_], I, E[_,_]](using c: Ccc.Aux[->, ⊙, E, Trivial, I], ip: IsInjective2[⊙], ie: IsInjective2[E])
  : Ccc.Aux[ArrowK2[->,*,*], ⊙, E, IsKind2, TypeK2[[a,b] =>> I]] =
    new CccArrowK2[->, ⊙, I, E] { val (assoc, inj, injE) = (c, ip, ie) }
  given ccc1[->[_,_], ⊙[_,_], I](using c: Ccc.Aux[->, ⊙, ->, Trivial, I], i: IsInjective2[⊙], ie: IsInjective2[->])
  : Ccc.Aux[ArrowK2[->,*,*], ⊙, ArrowK2[->,*,*], IsKind2, TypeK2[[a,b] =>> I]] =
    new Ccc1ArrowK2[->, ⊙, I] { val (assoc, inj, injE) = (c, i, ie) }
  given initial[->[_,_], I](using i: Initial.Aux[->, Trivial, I]): Initial.Aux[ArrowK2[->,*,*], IsKind2, TypeK2[[a,b] =>> I]] =
    new InitialArrowK2[->, I] { val ini = i }
  given terminal[->[_,_], T](using t: Terminal.Aux[->, Trivial, T]): Terminal.Aux[ArrowK2[->,*,*], IsKind2, TypeK2[[a,b] =>> T]] =
    new TerminalArrowK2[->, T] { val term = t }
}

trait ArrowK2Implicits01 extends ArrowK2Implicits02 {
  given subcat[->[_,_]](using s: Subcat.Aux[->, Trivial]): Subcat.Aux[ArrowK2[->,*,*], IsKind2] =
    new SubcatArrowK2[->] { val cat = s }
  given cartesian[->[_,_], ⊙[_,_], I](using c: Cartesian.Aux[->, ⊙, Trivial, I], i: IsInjective2[⊙])
  : Cartesian.Aux[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]] =
    new CartesianArrowK2[->, ⊙, I] { val (assoc, inj) = (c, i) }
  given coCartesian[->[_,_], ⊙[_,_], I](using c: Cartesian.Aux[Dual[->,*,*], ⊙, Trivial, I], i: IsInjective2[⊙])
  : Cartesian.Aux[Dual[ArrowK2[->,*,*],*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]] =
    new CoCartesianArrowK2[->, ⊙, I] { val (assoc, inj) = (c, i) }
}

trait ArrowK2Implicits02 extends ArrowK2Implicits03 {
  given semicat[->[_,_]](using s: Semicategory[->]): Semicategory[ArrowK2[->,*,*]] =
    new SemicategoryArrowK2[->] { val cat = s }
  given monoidal[->[_,_], ⊙[_,_], I](using m: Monoidal.Aux[->, ⊙, Trivial, I], i: IsInjective2[⊙])
  : Monoidal.Aux[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]] =
    new MonoidalArrowK2[->, ⊙, I] { val (assoc, inj) = (m, i) }
  given coMonoidal[->[_,_], ⊙[_,_], I](using m: Monoidal.Aux[Dual[->,*,*], ⊙, Trivial, I], i: IsInjective2[⊙])
  : Monoidal.Aux[Dual[ArrowK2[->,*,*],*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]] =
    new CoMonoidalArrowK2[->, ⊙, I] { val (assoc, inj) = (m, i) }
}

trait ArrowK2Implicits03 extends ArrowK2Implicits04 {
  given symmetric[->[_,_], ⊙[_,_]](using a: Symmetric.Aux[->, ⊙, Trivial], i: IsInjective2[⊙])
  : Symmetric.Aux[ArrowK2[->,*,*], ⊙, IsKind2] =
    new BraidedArrowK2[->, ⊙] with Symmetric[ArrowK2[->,*,*], ⊙] { val (assoc, inj) = (a, i) }
  given coSymmetric[->[_,_], ⊙[_,_]](using a: Symmetric.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙])
  : Symmetric.Aux[Dual[ArrowK2[->,*,*],*,*], ⊙, IsKind2] =
    new CoBraidedArrowK2[->, ⊙] with Symmetric[Dual[ArrowK2[->,*,*],*,*], ⊙] { val (assoc, inj)  = (a, i) }
}

trait ArrowK2Implicits04 extends ArrowK2Implicits05 {
  given braided[->[_,_], ⊙[_,_]](using a: Braided.Aux[->, ⊙, Trivial], i: IsInjective2[⊙]): Braided.Aux[ArrowK2[->,*,*], ⊙, IsKind2] =
    new BraidedArrowK2[->, ⊙] { val (assoc, inj) = (a, i) }
  given coBraided[->[_,_], ⊙[_,_]](using a: Braided.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙]): Braided.Aux[Dual[ArrowK2[->,*,*],*,*], ⊙, IsKind2] =
    new CoBraidedArrowK2[->, ⊙] { val (assoc, inj) = (a, i) }
}

trait ArrowK2Implicits05 {
  given associative[->[_,_], ⊙[_,_]](using a: Associative.Aux[->, ⊙, Trivial], i: IsInjective2[⊙]): Associative[ArrowK2[->,*,*], ⊙] =
    new AssociativeArrowK2[->, ⊙] { val (assoc, inj) = (a, i) }
  given coAssociative[->[_,_], ⊙[_,_]](using a: Associative.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙]): Associative[Dual[ArrowK2[->,*,*],*,*], ⊙] =
    new CoAssociativeArrowK2[->, ⊙] { val (assoc, inj) = (a, i) }
}

object ArrowK2Helpers:
  trait BifunctorArrowK2[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]]
    extends Exobifunctor[ArrowK2[==>,*,*], ArrowK2[-->,*,*], ArrowK2[>->,*,*], ⊙]:
    protected def bif: Exobifunctor[==>, -->, >->, ⊙]
    protected given inj: IsInjective2[⊙]
    def bimap[A, X, B, Y](l: ArrowK2[==>, A, X], r: ArrowK2[-->, B, Y]): ArrowK2[>->, A ⊙ B, X ⊙ Y] =
      ArrowK2.from[>->, A ⊙ B, X ⊙ Y](using
        IsKind2.pairInjectivity[⊙, A, B](using l.kindA, r.kindA),
        IsKind2.pairInjectivity[⊙, X, Y](using l.kindB, r.kindB)
      )(∀∀.of.fromH([a,b] => () => bif.bimap(l.fn[a,b], r.fn[a,b])))

  trait SemicategoryArrowK2[->[_,_]] extends Semicategory[ArrowK2[->,*,*]]:
    protected def cat: Semicategory[->]
    def andThen[A, B, C](ab: ArrowK2[->, A, B], bc: ArrowK2[->, B, C]): ArrowK2[->, A, C] =
      val fa: ∀∀[[a,b] =>> ab.TypeB[a,b] -> bc.TypeB[a,b]] =
        IsKind2.injectivity(ab.kindB, bc.kindA).flip.subst[[f[_,_]] =>> ∀∀[[a,b] =>> f[a,b] -> bc.TypeB[a,b]]](bc.fn)
      ArrowK2.from[->, A, C](using ab.kindA, bc.kindB)(∀∀.of.fromH([a,b] => () => cat.andThen(ab.fn[a,b], fa[a,b])))

  trait SubcatArrowK2[->[_,_]] extends SemicategoryArrowK2[->] with Subcat.Proto[ArrowK2[->,*,*], IsKind2]:
    override def cat: Subcat.Aux[->, Trivial]
    def id[A](using A: IsKind2[A]): ArrowK2[->, A, A] =
      ArrowK2(∀∀.from(new ∀∀.Prototype[[a,b] =>> A.Type[a,b] -> A.Type[a,b]] { def apply[a,b] = cat.id[A.Type[a,b]] }))

  trait DistributiveArrowK2[->[_,_], ⨂[_,_], ProductId, ⨁[_,_], SumId]
    extends SubcatArrowK2[->]
      with Distributive.Proto[ArrowK2[->,*,*], IsKind2, ⨂, TypeK2[[a,b] =>> ProductId], ⨁, TypeK2[[a,b] =>> SumId]]:
    override def cat: Distributive.Aux[->, Trivial, ⨂, ProductId, ⨁, SumId]
    given injP: IsInjective2[⨂]
    given injS: IsInjective2[⨁]
    given Cartesian.Aux[->, ⨂, Trivial, ProductId] = cat.cartesian
    given Cocartesian.Aux[->, ⨁, Trivial, SumId] = cat.cocartesian
    def cartesian: Cartesian.Aux[ArrowK2[->,*,*], ⨂, IsKind2, TypeK2[[a,b] =>> ProductId]] = summon
    def cocartesian: Cocartesian.Aux[ArrowK2[->,*,*], ⨁, IsKind2, TypeK2[[a,b] =>> SumId]] = summon
    def distribute[A, B, C](using ia: IsKind2[A], ib: IsKind2[B], ic: IsKind2[C]): ArrowK2[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]] =
      ArrowK2.from[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]](
        ∀∀.of.fromH([a,b] => () => cat.distribute[ia.Type[a,b], ib.Type[a,b], ic.Type[a,b]])
      )

  trait AssociativeArrowK2[->[_,_], ⊙[_,_]] extends Associative[ArrowK2[->,*,*], ⊙]:
    type TC[a] = IsKind2[a]
    protected def assoc: Associative.Aux[->, ⊙, Trivial]
    private given Endobifunctor[->, ⊙] = assoc.bifunctor
    private given Subcat.Aux[->, Trivial] = assoc.C
    protected given inj: IsInjective2[⊙]
    def C: Subcat.Aux[ArrowK2[->,*,*], IsKind2] = summon
    def bifunctor: Endobifunctor[ArrowK2[->,*,*], ⊙] = summon
    def associate  [A, B, C](using ia: IsKind2[A], ib: IsKind2[B], ic: IsKind2[C]): ArrowK2[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]] =
      ArrowK2.from[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]](
        ∀∀.of.fromH([a,b] => () => assoc.associate[ia.Type[a,b], ib.Type[a,b], ic.Type[a,b]])
      )
    def diassociate[A, B, C](using ia: IsKind2[A], ib: IsKind2[B], ic: IsKind2[C]): ArrowK2[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]] =
      ArrowK2.from[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]](
        ∀∀.of.fromH([a,b] => () => assoc.diassociate[ia.Type[a,b], ib.Type[a,b], ic.Type[a,b]])
      )

  trait CoAssociativeArrowK2[->[_,_], ⊙[_,_]] extends Associative[Dual[ArrowK2[->,*,*],*,*], ⊙]:
    type TC[a] = IsKind2[a]
    protected def assoc: Associative.Aux[Dual[->,*,*], ⊙, Trivial]
    private given Endobifunctor[Dual[->,*,*], ⊙] = assoc.bifunctor
    private given Subcat.Aux[Dual[->,*,*], Trivial] = assoc.C
    protected given inj: IsInjective2[⊙]
    def C: Subcat.Aux[[a,b] =>> Dual[ArrowK2[->,*,*],a,b], IsKind2] = summon
    def bifunctor: Endobifunctor[[a,b] =>> Dual[ArrowK2[->,*,*],a,b], ⊙] =
      val ff = Endobifunctor[ArrowK2[Dual[->,*,*],*,*], ⊙]
      IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Endobifunctor[f, ⊙]].isoMapK2(ArrowK2.invertDual)(ff)
    def associate[A, B, C](using ia: IsKind2[A], ib: IsKind2[B], ic: IsKind2[C]): Dual[ArrowK2[->,*,*], A ⊙ B ⊙ C, A ⊙ (B ⊙ C)] =
      Dual(ArrowK2.from[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]](
        ∀∀.of.fromH([a,b] => () => assoc.associate[ia.Type[a,b], ib.Type[a,b], ic.Type[a,b]])
      ))
    def diassociate[A, B, C](using ia: IsKind2[A], ib: IsKind2[B], ic: IsKind2[C]): Dual[ArrowK2[->,*,*], A ⊙ (B ⊙ C), A ⊙ B ⊙ C] =
      Dual(ArrowK2.from[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]](
        ∀∀.of.fromH([a,b] => () => assoc.diassociate[ia.Type[a,b], ib.Type[a,b], ic.Type[a,b]])
      ))

  trait BraidedArrowK2[->[_,_], ⊙[_,_]] extends AssociativeArrowK2[->, ⊙] with Braided.Proto[ArrowK2[->,*,*], ⊙, IsKind2]:
    protected def assoc: Braided.Aux[->, ⊙, Trivial]
    def braid[A, B](using ia: IsKind2[A], ib: IsKind2[B]): ArrowK2[->, A ⊙ B, B ⊙ A] =
      ArrowK2.from[->, A ⊙ B, B ⊙ A](∀∀.of.fromH([a,b] => () => assoc.braid[ia.Type[a,b], ib.Type[a,b]]))

  trait CoBraidedArrowK2[->[_,_], ⊙[_,_]]
    extends CoAssociativeArrowK2[->, ⊙]
      with Braided.Proto[Dual[ArrowK2[->,*,*],*,*], ⊙, IsKind2]:
    protected def assoc: Braided.Aux[Dual[->,*,*], ⊙, Trivial]
    def braid[A, B](using ia: IsKind2[A], ib: IsKind2[B]): Dual[ArrowK2[->,*,*], A ⊙ B, B ⊙ A] =
      Dual(ArrowK2.from[->, B ⊙ A, A ⊙ B](∀∀.of.fromH([a,b] => () => assoc.braid[ia.Type[a,b], ib.Type[a,b]])))

  trait MonoidalArrowK2[->[_,_], ⊙[_,_], I]
    extends AssociativeArrowK2[->, ⊙]
      with Monoidal.Proto[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]]:
    protected def assoc: Monoidal.Aux[->, ⊙, Trivial, I]
    def idl[A](using a: IsKind2[A]): ArrowK2[->, Id ⊙ A, A] =
      ArrowK2.from[->, Id ⊙ A, A](∀∀.of.fromH([a,b] => () => assoc.idl[a.Type[a,b]]))
    def coidl[A](using a: IsKind2[A]): ArrowK2[->, A, Id ⊙ A] =
      ArrowK2.from[->, A, Id ⊙ A](∀∀.of.fromH([a,b] => () => assoc.coidl[a.Type[a,b]]))
    def idr[A](using a: IsKind2[A]): ArrowK2[->, A ⊙ Id, A] =
      ArrowK2.from[->, A ⊙ Id, A](∀∀.of.fromH([a,b] => () => assoc.idr[a.Type[a,b]]))
    def coidr[A](using a: IsKind2[A]): ArrowK2[->, A, A ⊙ Id] =
      ArrowK2.from[->, A, A ⊙ Id](∀∀.of.fromH([a,b] => () => assoc.coidr[a.Type[a,b]]))

  trait CoMonoidalArrowK2[->[_,_], ⊙[_,_], I]
    extends CoAssociativeArrowK2[->, ⊙]
      with Monoidal.Proto[Dual[ArrowK2[->,*,*],*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]]:
    protected def assoc: Monoidal.Aux[Dual[->,*,*], ⊙, Trivial, I]
    def idl[A](using a: IsKind2[A]): Dual[ArrowK2[->,*,*], Id ⊙ A, A] =
      Dual(ArrowK2.from[->, A, Id ⊙ A](∀∀.of.fromH([a,b] => () => assoc.idl[a.Type[a,b]].toFn)))
    def coidl[A](using a: IsKind2[A]): Dual[ArrowK2[->,*,*], A, Id ⊙ A] =
      Dual(ArrowK2.from[->, Id ⊙ A, A](∀∀.of.fromH([a,b] => () => assoc.coidl[a.Type[a,b]].toFn)))
    def idr[A](using a: IsKind2[A]): Dual[ArrowK2[->,*,*], A ⊙ Id, A] =
      Dual(ArrowK2.from[->, A, A ⊙ Id](∀∀.of.fromH([a,b] => () => assoc.idr[a.Type[a,b]].toFn)))
    def coidr[A](using a: IsKind2[A]): Dual[ArrowK2[->,*,*], A, A ⊙ Id] =
      Dual(ArrowK2.from[->, A ⊙ Id, A](∀∀.of.fromH([a,b] => () => assoc.coidr[a.Type[a,b]].toFn)))

  trait CartesianArrowK2[->[_,_], ⊙[_,_], I]
    extends MonoidalArrowK2[->, ⊙, I]
      with BraidedArrowK2[->, ⊙]
      with Cartesian.Proto[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]]:
    protected def assoc: Cartesian.Aux[->, ⊙, Trivial, I]
    def fst[A, B](using a: IsKind2[A], b: IsKind2[B]): ArrowK2[->, A ⊙ B, A] =
      ArrowK2.from[->, A ⊙ B, A](∀∀.of.fromH([a,b] => () => assoc.fst[a.Type[a,b], b.Type[a,b]]))
    def snd[A, B](using a: IsKind2[A], b: IsKind2[B]): ArrowK2[->, A ⊙ B, B] =
      ArrowK2.from[->, A ⊙ B, B](∀∀.of.fromH([a,b] => () => assoc.snd[a.Type[a,b], b.Type[a,b]]))
    def diag[A](using a: IsKind2[A]): ArrowK2[->, A, A ⊙ A] =
      ArrowK2.from[->, A, A ⊙ A](∀∀.of.fromH([a,b] => () => assoc.diag[a.Type[a,b]]))
    def &&&[A, B, C](f: ArrowK2[->, A, B], g: ArrowK2[->, A, C]): ArrowK2[->, A, B ⊙ C] =
      given ia: IsKind2.Aux[A, f.TypeA] = f.kindA
      given ib: IsKind2.Aux[B, f.TypeB] = f.kindB
      given ic: IsKind2.Aux[C, g.TypeB] = g.kindB
      ArrowK2.from[->, A, B ⊙ C](
        ∀∀.of.fromH([a,b] => () => assoc.merge[ia.Type[a,b], ib.Type[a,b], ic.Type[a,b]](f.unapply[a,b], g.unapply[a,b]))
      )

  trait CoCartesianArrowK2[->[_,_], ⊙[_,_], I]
    extends CoMonoidalArrowK2[->, ⊙, I]
      with CoBraidedArrowK2[->, ⊙]
      with Cartesian.Proto[Dual[ArrowK2[->,*,*],*,*], ⊙, IsKind2, TypeK2[[a,b] =>> I]]:
    protected def assoc: Cartesian.Aux[Dual[->,*,*], ⊙, Trivial, I]
    def fst[A, B](using a: IsKind2[A], b: IsKind2[B]): Dual[ArrowK2[->,*,*], A ⊙ B, A] =
      Dual(ArrowK2.from[->, A, A ⊙ B](∀∀.of.fromH([a,b] => () => assoc.fst[a.Type[a,b], b.Type[a,b]])))
    def snd[A, B](using a: IsKind2[A], b: IsKind2[B]): Dual[ArrowK2[->,*,*], A ⊙ B, B] =
      Dual(ArrowK2.from[->, B, A ⊙ B](∀∀.of.fromH([a,b] => () => assoc.snd[a.Type[a,b], b.Type[a,b]])))
    def diag[A](using a: IsKind2[A]): Dual[ArrowK2[->,*,*], A, A ⊙ A] =
      Dual(ArrowK2.from[->, A ⊙ A, A](∀∀.of.fromH([a,b] => () => assoc.diag[a.Type[a,b]])))
    def &&&[A, B, C](f: Dual[ArrowK2[->,*,*], A, B], g: Dual[ArrowK2[->,*,*], A, C]): Dual[ArrowK2[->,*,*], A, B ⊙ C] =
      given ia: IsKind2[A] = f.toFn.kindB
      given ib: IsKind2[B] = f.toFn.kindA
      given ic: IsKind2[C] = g.toFn.kindA
      Dual(ArrowK2.from[->, B ⊙ C, A](
        ∀∀.of.fromH([a,b] => () => assoc.&&&[ia.Type[a,b], ib.Type[a,b], ic.Type[a,b]](Dual(f.toFn.unapply[a,b]), Dual(g.toFn.unapply[a,b])))
      ))

  trait InitialArrowK2[->[_,_], I0] extends Initial[ArrowK2[->,*,*]]:
    type TC[a] = IsKind2[a]
    type I = TypeK2[[a,b] =>> I0]
    protected def ini: Initial.Aux[->, Trivial, I0]
    def TC: IsKind2[I] = summon
    def subcat: Subcat.Aux[ArrowK2[->,*,*], IsKind2] = ArrowK2.subcat[->](using ini.subcat)
    def initiate[A](using a: IsKind2[A]): ArrowK2[->, I, A] =
      ArrowK2.from[->, I, A](∀∀.of.fromH([a,b] => () => ini.initiate[a.Type[a,b]]))

  trait TerminalArrowK2[->[_,_], T] extends Initial[[a,b] =>> Dual[ArrowK2[->,*,*], a, b]] {
    type TC[a] = IsKind2[a]
    type I = TypeK2[[a,b] =>> T]
    protected def term: Terminal.Aux[->, Trivial, T]
    def TC: IsKind2[I] = summon
    def subcat: Subcat.Aux[Dual[ArrowK2[->,*,*],*,*], IsKind2] =
      val sad = ArrowK2.subcat[Dual[->,*,*]](using term.subcat)
      IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Subcat.Aux[f, IsKind2]].isoMapK2(ArrowK2.invertDual)(sad)
    def initiate[A](using A: IsKind2[A]): Dual[ArrowK2[->,*,*], TypeK2[[a,b] =>> T], A] =
      Dual(ArrowK2.from[->, A, TypeK2[[a,b] =>> T]](∀∀.of.fromH([a,b] => () => term.terminate[A.Type[a,b]])))
  }

  trait CccArrowK2[->[_,_], ⊙[_,_], PI, E[_,_]]
    extends CartesianArrowK2[->, ⊙, PI]
      with Ccc.Proto[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[[a,b] =>> PI], E]:
    protected def assoc: Ccc.Aux[->, ⊙, E, Trivial, PI]
    protected given injE: IsInjective2[E]
    def curry[A, B, C](f: ArrowK2[->, A ⊙ B, C]): ArrowK2[->, A, E[B, C]] =
      val (ta: IsKind2[A], tb: IsKind2[B]) = f.kindA.pairInjectivity[⊙, A, B]
      given IsKind2.Aux[A, ta.Type] = ta
      given IsKind2.Aux[B, tb.Type] = tb
      given IsKind2.Aux[C, f.TypeB] = f.kindB
      ArrowK2.from[->, A, E[B, C]](∀∀.of.fromH([a,b] => () => assoc.curry[ta.Type[a,b], tb.Type[a,b], f.TypeB[a,b]](f.unapply[a,b])))
    def uncurry[A, B, C](f: ArrowK2[->, A, E[B, C]]): ArrowK2[->, A ⊙ B, C] =
      val (tb: IsKind2[B], tc: IsKind2[C]) = f.kindB.pairInjectivity[E, B, C]
      given IsKind2.Aux[A, f.TypeA] = f.kindA
      given IsKind2.Aux[B, tb.Type] = tb
      given IsKind2.Aux[C, tc.Type] = tc
      ArrowK2.from[->, A ⊙ B, C](∀∀.of.fromH([a,b] => () => assoc.uncurry[f.TypeA[a,b], tb.Type[a,b], tc.Type[a,b]](f.unapply[a,b])))

  trait Ccc1ArrowK2[->[_,_], ⊙[_,_], PI]
    extends CartesianArrowK2[->, ⊙, PI]
      with Ccc.Proto[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[[a,b] =>> PI], ArrowK2[->,*,*]]:
    protected def assoc: Ccc.Aux[->, ⊙, ->, Trivial, PI]
    protected given injE: IsInjective2[->]
    def curry[A, B, C](f: ArrowK2[->, A ⊙ B, C]): ArrowK2[->, A, ArrowK2[->, B, C]] =
      val (ta: IsKind2[A], tb: IsKind2[B]) = f.kindA.pairInjectivity[⊙, A, B]
      given IsKind2.Aux[A, ta.Type] = ta
      given IsKind2.Aux[B, tb.Type] = tb
      given IsKind2.Aux[C, f.TypeB] = f.kindB
      ArrowK2.from[->, A, ArrowK2[->, B, C]](
        ∀∀.of.fromH([a,b] => () => assoc.curry[ta.Type[a,b], tb.Type[a,b], f.TypeB[a,b]](f.unapply[a,b]))
      )
    def uncurry[A, B, C](f: ArrowK2[->, A, ArrowK2[->, B, C]]): ArrowK2[->, A ⊙ B, C] =
      given IsInjective2[ArrowK2[->,*,*]] = ArrowK2.isInjective[->]
      val (tb: IsKind2[B], tc: IsKind2[C]) = f.kindB.pairInjectivity[ArrowK2[->,*,*], B, C]
      given IsKind2.Aux[A, f.TypeA] = f.kindA
      given IsKind2.Aux[B, tb.Type] = tb
      given IsKind2.Aux[C, tc.Type] = tc
      ArrowK2.from[->, A ⊙ B, C](
        ∀∀.of.fromH([a,b] => () => assoc.uncurry[f.TypeA[a,b], tb.Type[a,b], tc.Type[a,b]](f.unapply[a,b]))
      )

end ArrowK2Helpers
