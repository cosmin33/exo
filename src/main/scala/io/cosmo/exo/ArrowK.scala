package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax.*

trait ArrowK[->[_,_], A, B]:
  type TypeA[_]
  type TypeB[_]
  def kindA: IsKind.Aux[A, TypeA]
  def kindB: IsKind.Aux[B, TypeB]
  def fn: ∀[[a] =>> TypeA[a] -> TypeB[a]]
  def unapply(using ia: IsKind[A], ib: IsKind[B]): ∀[[a] =>> ia.Type[a] -> ib.Type[a]] =
    IsK.lower2[[F[_], G[_]] =>> ∀[[a] =>> F[a] -> G[a]], TypeA, ia.Type, TypeB, ib.Type](
      IsKind.injectivity(kindA, ia),
      IsKind.injectivity(kindB, ib)
    )(fn)

object ArrowK extends ArrowKImplicits {
  type Aux[->[_,_], A, B, F[_], G[_]] = ArrowK[->, A, B] { type TypeA[x] = F[x]; type TypeB[x] = G[x] }
  def apply[->[_,_], A, B, F[_], G[_]](f: ∀[[a] =>> F[a] -> G[a]])(
    using ia: IsKind.Aux[A, F[_]], ib: IsKind.Aux[B, G[_]]
  ): ArrowK.Aux[->, A, B, F, G] =
    new ArrowK[->, A, B] { type TypeA[x] = F[x]; type TypeB[x] = G[x]; val (kindA, kindB, fn) = (ia, ib, f) }

  def from[->[_,_], A, B](using ia: IsKind[A], ib: IsKind[B]): MkArrowK[->, A, B, ia.Type, ib.Type] =
    new MkArrowK[->, A, B, ia.Type, ib.Type](ia, ib)
  case class MkArrowK[->[_,_], A, B, F[_], G[_]](ia: IsKind.Aux[A, F], ib: IsKind.Aux[B, G]):
    def apply(f: ∀[[a] =>> F[a] -> G[a]]): ArrowK.Aux[->, A, B, F, G] = ArrowK.apply[->, A, B, F, G](f)(using ia, ib)

  def isoFunKUnapply[->[_,_], A, B](i: Iso[ArrowK[->,*,*], A, B])(
    using a: IsKind[A], b: IsKind[B])(
    using s: Subcat[->]
  ): IsoK[->, a.Type, b.Type] = IsoK.unsafe(i.to.unapply, i.from.unapply)

  def isInjective[->[_,_]]: IsInjective2[ArrowK[->,*,*]] = IsInjective2.witness1[ArrowK[->,*,*], 1, 2, 3]

  given invertDual[->[_,_]]: (ArrowK[Dual[->,*,*],*,*] <~~> Dual[ArrowK[->,*,*],*,*]) =
    <~~>.unsafe([A, B] => () =>
      <=>.unsafe[ArrowK[Dual[->,*,*],A,B], Dual[ArrowK[->,*,*],A,B]](
        ad => Dual(ArrowK.from(using ad.kindB, ad.kindA)(∀.of.fromH([a] => () => ad.fn[a].toFn))),
        da => ArrowK.from(using da.kindB, da.kindA)(∀.of.fromH([a] => () => Dual(da.fn[a])))
      )
    )

  given isoArrowKCanonic[->[_,_], A, B](using a: IsKind[A], b: IsKind[B])
  : (ArrowK[->, A, B] <=> ∀[[a] =>> a.Type[a] -> b.Type[a]]) =
    Iso.unsafe(_.unapply, apply)

  given isoIsoArrowKCanonic[->[_,_], A, B](using a: IsKind[A], b: IsKind[B])(using s: Subcat.Aux[->, Trivial])
  : (Iso[ArrowK[->,*,*], A, B] <=> IsoK[->, a.Type, b.Type]) =
    Iso.unsafe(i => IsoK.unsafe(i.to.unapply, i.from.unapply), i => Iso.unsafe(apply(i.to), apply(i.from)))

}

import ArrowKHelpers.*

trait ArrowKImplicits extends ArrowKImplicits01 {
  given bifunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]](using b: Exobifunctor[==>, -->, >->, ⊙], i: IsInjective2[⊙])
  : Exobifunctor[ArrowK[==>,*,*], ArrowK[-->,*,*], ArrowK[>->,*,*], ⊙] =
    new BifunctorArrowK[==>, -->, >->, ⊙] { val (bif, inj) = (b, i) }
  given distributive[->[_,_], ⨂[_,_], ProductId, ⨁[_,_], SumId](using
    s: Distributive.Aux[->, Trivial, ⨂, ProductId, ⨁, SumId], ip: IsInjective2[⨂], is: IsInjective2[⨁]
  ): Distributive.Aux[ArrowK[->,*,*], IsKind, ⨂, TypeK[[a] =>> ProductId], ⨁, TypeK[[a] =>> SumId]] =
    new DistributiveArrowK[->, ⨂, ProductId, ⨁, SumId] { val (cat, injP, injS) = (s, ip, is) }
  given ccc[->[_,_], ⊙[_,_], I, E[_,_]](using c: Ccc.Aux[->, ⊙, E, Trivial, I], ip: IsInjective2[⊙], ie: IsInjective2[E])
  : Ccc.Aux[ArrowK[->,*,*], ⊙, E, IsKind, TypeK[[a] =>> I]] =
    new CccArrowK[->, ⊙, I, E] { val (assoc, inj, injE) = (c, ip, ie) }
  given ccc1[->[_,_], ⊙[_,_], I](using c: Ccc.Aux[->, ⊙, ->, Trivial, I], i: IsInjective2[⊙], ie: IsInjective2[->])
  : Ccc.Aux[ArrowK[->,*,*], ⊙, ArrowK[->,*,*], IsKind, TypeK[[a] =>> I]] =
    new Ccc1ArrowK[->, ⊙, I] { val (assoc, inj, injE) = (c, i, ie) }
  given initial[->[_,_], I](using i: Initial.Aux[->, Trivial, I]): Initial.Aux[ArrowK[->,*,*], IsKind, TypeK[[a] =>> I]] =
    new InitialArrowK[->, I] { val ini = i }
  given terminal[->[_,_], T](using t: Terminal.Aux[->, Trivial, T]): Terminal.Aux[ArrowK[->,*,*], IsKind, TypeK[[a] =>> T]] =
    new TerminalArrowK[->, T] { val term = t }
}

trait ArrowKImplicits01 extends ArrowKImplicits02 {
  given subcat[->[_,_]](using s: Subcat.Aux[->, Trivial]): Subcat.Aux[ArrowK[->,*,*], IsKind] =
    new SubcatArrowK[->] { val cat = s }
  given cartesian[->[_,_], ⊙[_,_], I](using c: Cartesian.Aux[->, ⊙, Trivial, I], i: IsInjective2[⊙])
  : Cartesian.Aux[ArrowK[->,*,*], ⊙, IsKind, TypeK[[a] =>> I]] =
    new CartesianArrowK[->, ⊙, I] { val (assoc, inj) = (c, i) }
  given coCartesian[->[_,_], ⊙[_,_], I](using c: Cartesian.Aux[Dual[->,*,*], ⊙, Trivial, I], i: IsInjective2[⊙])
  : Cartesian.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind, TypeK[[a] =>> I]] =
    new CoCartesianArrowK[->, ⊙, I] { val (assoc, inj) = (c, i) }
}

trait ArrowKImplicits02 extends ArrowKImplicits03 {
  given semicat[->[_,_]](using s: Semicategory[->]): Semicategory[ArrowK[->,*,*]] =
    new SemicategoryArrowK[->] { val cat = s }
  given monoidal[->[_,_], ⊙[_,_], I](using m: Monoidal.Aux[->, ⊙, Trivial, I], i: IsInjective2[⊙])
  : Monoidal.Aux[ArrowK[->,*,*], ⊙, IsKind, TypeK[[a] =>> I]] =
    new MonoidalArrowK[->, ⊙, I] { val (assoc, inj) = (m, i) }
  given coMonoidal[->[_,_], ⊙[_,_], I](using m: Monoidal.Aux[Dual[->,*,*], ⊙, Trivial, I], i: IsInjective2[⊙])
  : Monoidal.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind, TypeK[[a] =>> I]] =
    new CoMonoidalArrowK[->, ⊙, I] { val (assoc, inj) = (m, i) }
}

trait ArrowKImplicits03 extends ArrowKImplicits04 {
  given symmetric[->[_,_], ⊙[_,_]](using a: Symmetric.Aux[->, ⊙, Trivial], i: IsInjective2[⊙])
  : Symmetric.Aux[ArrowK[->,*,*], ⊙, IsKind] =
    new BraidedArrowK[->, ⊙] with Symmetric[ArrowK[->,*,*], ⊙] { val (assoc, inj) = (a, i) }
  given coSymmetric[->[_,_], ⊙[_,_]](using a: Symmetric.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙])
  : Symmetric.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind] =
    new CoBraidedArrowK[->, ⊙] with Symmetric[Dual[ArrowK[->,*,*],*,*], ⊙] { val (assoc, inj)  = (a, i) }
}

trait ArrowKImplicits04 extends ArrowKImplicits05 {
  given braided[->[_,_], ⊙[_,_]](using a: Braided.Aux[->, ⊙, Trivial], i: IsInjective2[⊙]): Braided.Aux[ArrowK[->,*,*], ⊙, IsKind] =
    new BraidedArrowK[->, ⊙] { val (assoc, inj) = (a, i) }
  given coBraided[->[_,_], ⊙[_,_]](using a: Braided.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙]): Braided.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind] =
    new CoBraidedArrowK[->, ⊙] { val (assoc, inj) = (a, i) }
}

trait ArrowKImplicits05 {
  given associative[->[_,_], ⊙[_,_]](using a: Associative.Aux[->, ⊙, Trivial], i: IsInjective2[⊙]): Associative[ArrowK[->,*,*], ⊙] =
    new AssociativeArrowK[->, ⊙] { val (assoc, inj) = (a, i) }
  given coAssociative[->[_,_], ⊙[_,_]](using a: Associative.Aux[Dual[->,*,*], ⊙, Trivial], i: IsInjective2[⊙]): Associative[Dual[ArrowK[->,*,*],*,*], ⊙] =
    new CoAssociativeArrowK[->, ⊙] { val (assoc, inj) = (a, i) }
}

object ArrowKHelpers:
  trait BifunctorArrowK[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]]
    extends Exobifunctor[ArrowK[==>,*,*], ArrowK[-->,*,*], ArrowK[>->,*,*], ⊙]:
    protected def bif: Exobifunctor[==>, -->, >->, ⊙]
    protected given inj: IsInjective2[⊙]
    def bimap[A, X, B, Y](l: ArrowK[==>, A, X], r: ArrowK[-->, B, Y]): ArrowK[>->, A ⊙ B, X ⊙ Y] =
      ArrowK.from[>->, A ⊙ B, X ⊙ Y](using
        IsKind.pairInjectivity[⊙, A, B](using l.kindA, r.kindA),
        IsKind.pairInjectivity[⊙, X, Y](using l.kindB, r.kindB)
      )(∀.of.fromH([a] => () => bif.bimap(l.fn[a], r.fn[a])))


  trait SemicategoryArrowK[->[_,_]] extends Semicategory[ArrowK[->,*,*]]:
    protected def cat: Semicategory[->]
    def andThen[A, B, C](ab: ArrowK[->, A, B], bc: ArrowK[->, B, C]): ArrowK[->, A, C] =
      val fa: ∀[[a] =>> ab.TypeB[a] -> bc.TypeB[a]] =
        IsKind.injectivity(ab.kindB, bc.kindA).flip.subst[[f[_]] =>> ∀[[a] =>> f[a] -> bc.TypeB[a]]](bc.fn)
      ArrowK.from[->, A, C](using ab.kindA, bc.kindB)(∀.of.fromH([a] => () => cat.andThen(ab.fn[a], fa[a])))

  trait SubcatArrowK[->[_,_]] extends SemicategoryArrowK[->] with Subcat.Proto[ArrowK[->,*,*], IsKind]:
    override def cat: Subcat.Aux[->, Trivial]
    def id[A](using A: IsKind[A]): ArrowK[->, A, A] =
      ArrowK(∀.from(new ∀.Prototype[[a] =>> A.Type[a] -> A.Type[a]] { def apply[a] = cat.id[A.Type[a]] }))

  trait DistributiveArrowK[->[_,_], ⨂[_,_], ProductId, ⨁[_,_], SumId]
    extends SubcatArrowK[->]
      with Distributive.Proto[ArrowK[->,*,*], IsKind, ⨂, TypeK[[a] =>> ProductId], ⨁, TypeK[[a] =>> SumId]]:
    override def cat: Distributive.Aux[->, Trivial, ⨂, ProductId, ⨁, SumId]
    given injP: IsInjective2[⨂]
    given injS: IsInjective2[⨁]
    given Cartesian.Aux[->, ⨂, Trivial, ProductId] = cat.cartesian
    given Cocartesian.Aux[->, ⨁, Trivial, SumId] = cat.cocartesian
    def cartesian: Cartesian.Aux[ArrowK[->,*,*], ⨂, IsKind, TypeK[[a] =>> ProductId]] = summon
    def cocartesian: Cocartesian.Aux[ArrowK[->,*,*], ⨁, IsKind, TypeK[[a] =>> SumId]] = summon
    def distribute[A, B, C](using ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): ArrowK[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]] =
      ArrowK.from[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]](
        ∀.of.fromH([a] => () => cat.distribute[ia.Type[a], ib.Type[a], ic.Type[a]])
      )

  trait AssociativeArrowK[->[_,_], ⊙[_,_]] extends Associative[ArrowK[->,*,*], ⊙]:
    type TC[a] = IsKind[a]
    protected def assoc: Associative.Aux[->, ⊙, Trivial]
    private given Endobifunctor[->, ⊙] = assoc.bifunctor
    private given Subcat.Aux[->, Trivial] = assoc.C
    protected given inj: IsInjective2[⊙]
    def C: Subcat.Aux[ArrowK[->,*,*], IsKind] = summon
    def bifunctor: Endobifunctor[ArrowK[->,*,*], ⊙] = summon
    def associate  [A, B, C](using ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): ArrowK[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]] =
      ArrowK.from[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]](
        ∀.of.fromH([a] => () => assoc.associate[ia.Type[a], ib.Type[a], ic.Type[a]])
      )
    def diassociate[A, B, C](using ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): ArrowK[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]] =
      ArrowK.from[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]](
        ∀.of.fromH([a] => () => assoc.diassociate[ia.Type[a], ib.Type[a], ic.Type[a]])
      )

  trait CoAssociativeArrowK[->[_,_], ⊙[_,_]] extends Associative[Dual[ArrowK[->,*,*],*,*], ⊙]:
    type TC[a] = IsKind[a]
    protected def assoc: Associative.Aux[Dual[->,*,*], ⊙, Trivial]
    private given Endobifunctor[Dual[->,*,*], ⊙] = assoc.bifunctor
    private given Subcat.Aux[Dual[->,*,*], Trivial] = assoc.C
    protected given inj: IsInjective2[⊙]
    def C: Subcat.Aux[[a,b] =>> Dual[ArrowK[->,*,*],a,b], IsKind] = summon
    def bifunctor: Endobifunctor[[a,b] =>> Dual[ArrowK[->,*,*],a,b], ⊙] =
      val ff = Endobifunctor[ArrowK[Dual[->,*,*],*,*], ⊙]
      IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Endobifunctor[f, ⊙]].isoMapK2(ArrowK.invertDual)(ff)
    def associate[A, B, C](using ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): Dual[ArrowK[->,*,*], A ⊙ B ⊙ C, A ⊙ (B ⊙ C)] =
      Dual(ArrowK.from[->, ⊙[A, ⊙[B, C]], ⊙[⊙[A, B], C]](
        ∀.of.fromH([a] => () => assoc.associate[ia.Type[a], ib.Type[a], ic.Type[a]])
      ))
    def diassociate[A, B, C](using ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): Dual[ArrowK[->,*,*], A ⊙ (B ⊙ C), A ⊙ B ⊙ C] =
      Dual(ArrowK.from[->, ⊙[⊙[A, B], C], ⊙[A, ⊙[B, C]]](
        ∀.of.fromH([a] => () => assoc.diassociate[ia.Type[a], ib.Type[a], ic.Type[a]])
      ))

  trait BraidedArrowK[->[_,_], ⊙[_,_]] extends AssociativeArrowK[->, ⊙] with Braided.Proto[ArrowK[->,*,*], ⊙, IsKind]:
    protected def assoc: Braided.Aux[->, ⊙, Trivial]
    def braid[A, B](using ia: IsKind[A], ib: IsKind[B]): ArrowK[->, A ⊙ B, B ⊙ A] =
      ArrowK.from[->, A ⊙ B, B ⊙ A](∀.of.fromH([a] => () => assoc.braid[ia.Type[a], ib.Type[a]]))

  trait CoBraidedArrowK[->[_,_], ⊙[_,_]]
    extends CoAssociativeArrowK[->, ⊙]
      with Braided.Proto[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind]:
    protected def assoc: Braided.Aux[Dual[->,*,*], ⊙, Trivial]
    def braid[A, B](using ia: IsKind[A], ib: IsKind[B]): Dual[ArrowK[->,*,*], A ⊙ B, B ⊙ A] =
      Dual(ArrowK.from[->, B ⊙ A, A ⊙ B](∀.of.fromH([a] => () => assoc.braid[ia.Type[a], ib.Type[a]])))

  trait MonoidalArrowK[->[_,_], ⊙[_,_], I]
    extends AssociativeArrowK[->, ⊙]
      with Monoidal.Proto[ArrowK[->,*,*], ⊙, IsKind, TypeK[[a] =>> I]]:
    protected def assoc: Monoidal.Aux[->, ⊙, Trivial, I]
    def idl[A](using a: IsKind[A]): ArrowK[->, Id ⊙ A, A] =
      ArrowK.from[->, Id ⊙ A, A](∀.of.fromH([a] => () => assoc.idl[a.Type[a]]))
    def coidl[A](using a: IsKind[A]): ArrowK[->, A, Id ⊙ A] =
      ArrowK.from[->, A, Id ⊙ A](∀.of.fromH([a] => () => assoc.coidl[a.Type[a]]))
    def idr[A](using a: IsKind[A]): ArrowK[->, A ⊙ Id, A] =
      ArrowK.from[->, A ⊙ Id, A](∀.of.fromH([a] => () => assoc.idr[a.Type[a]]))
    def coidr[A](using a: IsKind[A]): ArrowK[->, A, A ⊙ Id] =
      ArrowK.from[->, A, A ⊙ Id](∀.of.fromH([a] => () => assoc.coidr[a.Type[a]]))

  trait CoMonoidalArrowK[->[_,_], ⊙[_,_], I]
    extends CoAssociativeArrowK[->, ⊙]
      with Monoidal.Proto[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind, TypeK[[a] =>> I]]:
    protected def assoc: Monoidal.Aux[Dual[->,*,*], ⊙, Trivial, I]
    def idl[A](using a: IsKind[A]): Dual[ArrowK[->,*,*], Id ⊙ A, A] =
      Dual(ArrowK.from[->, A, Id ⊙ A](∀.of.fromH([a] => () => assoc.idl[a.Type[a]].toFn)))
    def coidl[A](using a: IsKind[A]): Dual[ArrowK[->,*,*], A, Id ⊙ A] =
      Dual(ArrowK.from[->, Id ⊙ A, A](∀.of.fromH([a] => () => assoc.coidl[a.Type[a]].toFn)))
    def idr[A](using a: IsKind[A]): Dual[ArrowK[->,*,*], A ⊙ Id, A] =
      Dual(ArrowK.from[->, A, A ⊙ Id](∀.of.fromH([a] => () => assoc.idr[a.Type[a]].toFn)))
    def coidr[A](using a: IsKind[A]): Dual[ArrowK[->,*,*], A, A ⊙ Id] =
      Dual(ArrowK.from[->, A ⊙ Id, A](∀.of.fromH([a] => () => assoc.coidr[a.Type[a]].toFn)))

  trait CartesianArrowK[->[_,_], ⊙[_,_], I]
    extends MonoidalArrowK[->, ⊙, I]
      with BraidedArrowK[->, ⊙]
      with Cartesian.Proto[ArrowK[->,*,*], ⊙, IsKind, TypeK[[a] =>> I]]:
    protected def assoc: Cartesian.Aux[->, ⊙, Trivial, I]
    def fst[A, B](using a: IsKind[A], b: IsKind[B]): ArrowK[->, A ⊙ B, A] =
      ArrowK.from[->, A ⊙ B, A](∀.of.fromH([a] => () => assoc.fst[a.Type[a], b.Type[a]]))
    def snd[A, B](using a: IsKind[A], b: IsKind[B]): ArrowK[->, A ⊙ B, B] =
      ArrowK.from[->, A ⊙ B, B](∀.of.fromH([a] => () => assoc.snd[a.Type[a], b.Type[a]]))
    def diag[A](using a: IsKind[A]): ArrowK[->, A, A ⊙ A] =
      ArrowK.from[->, A, A ⊙ A](∀.of.fromH([a] => () => assoc.diag[a.Type[a]]))
    def &&&[A, B, C](f: ArrowK[->, A, B], g: ArrowK[->, A, C]): ArrowK[->, A, B ⊙ C] =
      given ia: IsKind.Aux[A, f.TypeA] = f.kindA
      given ib: IsKind.Aux[B, f.TypeB] = f.kindB
      given ic: IsKind.Aux[C, g.TypeB] = g.kindB
      ArrowK.from[->, A, B ⊙ C](
        ∀.of.fromH([a] => () => assoc.merge[ia.Type[a], ib.Type[a], ic.Type[a]](f.unapply[a], g.unapply[a]))
      )

  trait CoCartesianArrowK[->[_,_], ⊙[_,_], I]
    extends CoMonoidalArrowK[->, ⊙, I]
      with CoBraidedArrowK[->, ⊙]
      with Cartesian.Proto[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind, TypeK[[a] =>> I]]:
    protected def assoc: Cartesian.Aux[Dual[->,*,*], ⊙, Trivial, I]
    def fst[A, B](using a: IsKind[A], b: IsKind[B]): Dual[ArrowK[->,*,*], A ⊙ B, A] =
      Dual(ArrowK.from[->, A, A ⊙ B](∀.of.fromH([a] => () => assoc.fst[a.Type[a], b.Type[a]])))
    def snd[A, B](using a: IsKind[A], b: IsKind[B]): Dual[ArrowK[->,*,*], A ⊙ B, B] =
      Dual(ArrowK.from[->, B, A ⊙ B](∀.of.fromH([a] => () => assoc.snd[a.Type[a], b.Type[a]])))
    def diag[A](using a: IsKind[A]): Dual[ArrowK[->,*,*], A, A ⊙ A] =
      Dual(ArrowK.from[->, A ⊙ A, A](∀.of.fromH([a] => () => assoc.diag[a.Type[a]])))
    def &&&[A, B, C](f: Dual[ArrowK[->,*,*], A, B], g: Dual[ArrowK[->,*,*], A, C]): Dual[ArrowK[->,*,*], A, B ⊙ C] =
      given ia: IsKind[A] = f.toFn.kindB
      given ib: IsKind[B] = f.toFn.kindA
      given ic: IsKind[C] = g.toFn.kindA
      Dual(ArrowK.from[->, B ⊙ C, A](
        ∀.of.fromH([a] => () => assoc.&&&[ia.Type[a], ib.Type[a], ic.Type[a]](Dual(f.toFn.unapply[a]), Dual(g.toFn.unapply[a])))
      ))

  trait InitialArrowK[->[_,_], I0] extends Initial[ArrowK[->,*,*]]:
    type TC[a] = IsKind[a]
    type I = TypeK[[x] =>> I0]
    protected def ini: Initial.Aux[->, Trivial, I0]
    def TC: IsKind[I] = summon
    def subcat: Subcat.Aux[ArrowK[->,*,*], IsKind] = ArrowK.subcat[->](using ini.subcat)
    def initiate[A](using a: IsKind[A]): ArrowK[->, I, A] =
      ArrowK.from[->, I, A](∀.of.fromH([a] => () => ini.initiate[a.Type[a]]))

  trait TerminalArrowK[->[_,_], T] extends Initial[[a,b] =>> Dual[ArrowK[->,*,*], a, b]] {
    type TC[a] = IsKind[a]
    type I = TypeK[[a] =>> T]
    protected def term: Terminal.Aux[->, Trivial, T]
    def TC: IsKind[I] = summon
    def subcat: Subcat.Aux[Dual[ArrowK[->,*,*],*,*], IsKind] =
      val sad = ArrowK.subcat[Dual[->,*,*]](using term.subcat)
      IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Subcat.Aux[f, IsKind]].isoMapK2(ArrowK.invertDual)(sad)
    def initiate[A](using A: IsKind[A]): Dual[ArrowK[->,*,*], TypeK[[a] =>> T], A] =
      Dual(ArrowK.from[->, A, TypeK[[a] =>> T]](∀.of.fromH([a] => () => term.terminate[A.Type[a]])))
  }

  trait CccArrowK[->[_,_], ⊙[_,_], PI, E[_,_]]
    extends CartesianArrowK[->, ⊙, PI]
      with Ccc.Proto[ArrowK[->,*,*], ⊙, IsKind, TypeK[[a] =>> PI], E]:
    protected def assoc: Ccc.Aux[->, ⊙, E, Trivial, PI]
    protected given injE: IsInjective2[E]
    def curry[A, B, C](f: ArrowK[->, A ⊙ B, C]): ArrowK[->, A, E[B, C]] =
      val (ta: IsKind[A], tb: IsKind[B]) = f.kindA.pairInjectivity[⊙, A, B]
      given IsKind.Aux[A, ta.Type] = ta
      given IsKind.Aux[B, tb.Type] = tb
      given IsKind.Aux[C, f.TypeB] = f.kindB
      ArrowK.from[->, A, E[B, C]](∀.of.fromH([a] => () => assoc.curry[ta.Type[a], tb.Type[a], f.TypeB[a]](f.unapply[a])))
    def uncurry[A, B, C](f: ArrowK[->, A, E[B, C]]): ArrowK[->, A ⊙ B, C] =
      val (tb: IsKind[B], tc: IsKind[C]) = f.kindB.pairInjectivity[E, B, C]
      given IsKind.Aux[A, f.TypeA] = f.kindA
      given IsKind.Aux[B, tb.Type] = tb
      given IsKind.Aux[C, tc.Type] = tc
      ArrowK.from[->, A ⊙ B, C](∀.of.fromH([a] => () => assoc.uncurry[f.TypeA[a], tb.Type[a], tc.Type[a]](f.unapply[a])))

  trait Ccc1ArrowK[->[_,_], ⊙[_,_], PI]
    extends CartesianArrowK[->, ⊙, PI]
      with Ccc.Proto[ArrowK[->,*,*], ⊙, IsKind, TypeK[[a] =>> PI], ArrowK[->,*,*]]:
    protected def assoc: Ccc.Aux[->, ⊙, ->, Trivial, PI]
    protected given injE: IsInjective2[->]
    def curry[A, B, C](f: ArrowK[->, A ⊙ B, C]): ArrowK[->, A, ArrowK[->, B, C]] =
      val (ta: IsKind[A], tb: IsKind[B]) = f.kindA.pairInjectivity[⊙, A, B]
      given IsKind.Aux[A, ta.Type] = ta
      given IsKind.Aux[B, tb.Type] = tb
      given IsKind.Aux[C, f.TypeB] = f.kindB
      ArrowK.from[->, A, ArrowK[->, B, C]](
        ∀.of.fromH([a] => () => assoc.curry[ta.Type[a], tb.Type[a], f.TypeB[a]](f.unapply[a]))
      )
    def uncurry[A, B, C](f: ArrowK[->, A, ArrowK[->, B, C]]): ArrowK[->, A ⊙ B, C] =
      given IsInjective2[ArrowK[->,*,*]] = ArrowK.isInjective[->]
      val (tb: IsKind[B], tc: IsKind[C]) = f.kindB.pairInjectivity[ArrowK[->,*,*], B, C]
      given IsKind.Aux[A, f.TypeA] = f.kindA
      given IsKind.Aux[B, tb.Type] = tb
      given IsKind.Aux[C, tc.Type] = tc
      ArrowK.from[->, A ⊙ B, C](
        ∀.of.fromH([a] => () => assoc.uncurry[f.TypeA[a], tb.Type[a], tc.Type[a]](f.unapply[a]))
      )

end ArrowKHelpers
