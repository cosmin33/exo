package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._
import io.cosmo.exo.internal._

trait Exobifunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]] { self =>
  def bimap[A, X, B, Y](left: A ==> X, right: B --> Y): ⊙[A, B] >-> ⊙[X, Y]

  def leftMap [A, B, Z](fn: A ==> Z)(using C: SubcatHasId[-->, B]): ⊙[A, B] >-> ⊙[Z, B] = bimap(fn, C.id)
  def rightMap[A, B, Z](fn: B --> Z)(using C: SubcatHasId[==>, A]): ⊙[A, B] >-> ⊙[A, Z] = bimap(C.id, fn)

  def leftFunctor [X](using C: SubcatHasId[-->, X]): Exo[==>, >->, ⊙[*, X]] =
    Exo.unsafe[==>, >->, ⊙[*, X]]([a, b] => (fn: a ==> b) => leftMap(fn))
  def rightFunctor[X](using C: SubcatHasId[==>, X]): Exo[-->, >->, ⊙[X, *]] =
    Exo.unsafe[-->, >->, ⊙[X, *]]([a, b] => (fn: a --> b) => rightMap(fn))

  def leftForall [T[_]](using C: Subcat.Aux[-->, T]): T ~> ([x] =>> Exo[==>, >->, ⊙[*, x]]) =
    ~>([A] => (ta: T[A]) => leftFunctor(using SubcatHasId.from(using C, ta)))
  def rightForall[T[_]](using C: Subcat.Aux[==>, T]): T ~> ([x] =>> Exo[-->, >->, ⊙[x, *]]) =
    ~>([A] => (ta: T[A]) => rightFunctor(using SubcatHasId.from(using C, ta)))

}

object Exobifunctor extends ExobifunctorInstances 
  with DualBifunctorInstances 
  with EvidenceCatBifunctorInstances
  with ProdcatBifunctorInstances {

  type Con[==>[_,_], -->[_,_], >->[_,_], B[_,_]] = Exobifunctor[Dual[==>,*,*], Dual[-->,*,*], >->, B]
  type ConF[B[_,_]] = Con[* => *, * => *, * => *, B]

  def apply[=>:[_,_], ->:[_,_], ~>:[_,_], ⊙[_,_]](using bi: Exobifunctor[=>:, ->:, ~>:, ⊙]): Exobifunctor[=>:, ->:, ~>:, ⊙] = bi

  def fromFaFunctors[==>[_,_], -->[_,_], >->[_,_]: Semicategory, Bi[_,_]](
   L: ∀[[a] =>> Exo[==>, >->, Bi[*, a]]],
   R: ∀[[a] =>> Exo[-->, >->, Bi[a, *]]]
 ): Exobifunctor[==>, -->, >->, Bi] =
    new Exobifunctor[==>, -->, >->, Bi]:
      def bimap[A, X, B, Y](l: A ==> X, r: B --> Y): Bi[A, B] >-> Bi[X, Y] = L[B].map(l) >>> R[X].map(r)
      override def leftMap [A, B, Z](fn:  A ==> Z)(using C:  SubcatHasId[-->, B]) = L[B].map(fn)
      override def rightMap[A, B, Z](fn:  B --> Z)(using C:  SubcatHasId[==>, A]) = R[A].map(fn)

  extension[==>[_,_], >->[_,_], F[_,_]](self: Exobifunctor[==>, ==>, >->, F])
    def compose[G[_,_]](using G: Endobifunctor[==>, G]): Exobifunctor[==>, ==>, >->, [α, β] =>> F[G[α, β], G[α, β]]] =
      new Exobifunctor[==>, ==>, >->, [α, β] =>> F[G[α, β], G[α, β]]]:
        def bimap[A, X, B, Y](l: A ==> X, r: B ==> Y) = G.bimap(l, r) |> (i => self.bimap(i, i))

  def dual[->[_,_], Bi[_,_]](F: Endobifunctor[->, Bi]): Endobifunctor[Dual[->,*,*], Bi] =
    new Endobifunctor[Dual[->,*,*], Bi]:
      def bimap[A, X, B, Y](l: Dual[->, A, X], r: Dual[->, B, Y]): Dual[->, Bi[A, B], Bi[X, Y]] = Dual(F.bimap(l, r))

  def opp[->[_,_], Bi[_,_]](F: Endobifunctor[->, Bi]): Endobifunctor[Opp[->], Bi] =
    Dual.leibniz[->].flip.subst[[f[_,_]] =>> Endobifunctor[f, Bi]](dual(F))

  private[exo] def dicatToIso[==>[_,_], -->[_,_], >->[_,_], Bi[_,_], TC[_]](
    E: Exobifunctor[Dicat[==>,*,*], Dicat[-->,*,*], >->, Bi]
  )(using
    S1: Subcat.Aux[==>, TC],
    S2: Subcat.Aux[-->, TC],
  ): Exobifunctor[Iso[==>,*,*], Iso[-->,*,*], >->, Bi] =
    new Exobifunctor[Iso[==>,*,*], Iso[-->,*,*], >->, Bi]:
      override def bimap[A, X, B, Y](left: Iso[==>, A, X], right: Iso[-->, B, Y]) =
        E.bimap(Dicat[==>, A, X](left.to, left.from), Dicat[-->, B, Y](right.to, right.from))
}

object Endobifunctor {
  def apply[->[_,_], Bi[_,_]](using e: Endobifunctor[->, Bi]): Endobifunctor[->, Bi] = e
}

trait ExobifunctorInstances {

  given semicatToExobifunctor[->[_,_]](using s: Semicategory[->]): Exobifunctor[Dual[->,*,*], ->, Function, ->] =
    new Exobifunctor[Dual[->,*,*], ->, * => *, ->]:
      def bimap[A, X, B, Y](left: Dual[->, A, X], right: B -> Y): (A -> B) => (X -> Y) = left.toFn >>> _ >>> right

  given arrowEndofunctor[->[_,_], P[_,_]]: IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Endobifunctor[f, P]] =
    new IsoFunctorK2.ProtoF[[f[_,_]] =>> Endobifunctor[f, P]]:
      protected def mapK2[F[_,_], G[_,_]](iso: F <~~> G): Endobifunctor[F, P] => Endobifunctor[G, P] = ef =>
        new Endobifunctor[G, P]:
          def bimap[A, X, B, Y](l: G[A, X], r: G[B, Y]): G[P[A, B], P[X, Y]] =
            iso.to(ef.bimap(iso.from(l), iso.from(r)))

  given profunctor[->[_,_]: Semicategory]: Exobifunctor[Dual[->,*,*], ->, * => *, ->] =
    new Exobifunctor[Dual[->,*,*], ->, * => *, ->]:
      def bimap[A, X, B, Y](left: Dual[->, A, X], right: B -> Y): A -> B => (X -> Y) = f => left.toFn >>> f >>> right

  given tuple2: EndobifunctorF[Tuple2] =
    new Endobifunctor[* => *, Tuple2]:
      override def bimap[A, X, B, Y](l: A => X, r: B => Y): ((A, B)) => (X, Y) =
        (a, b) => (l(a), r(b))

  given either: EndobifunctorF[Either] =
    new Endobifunctor[* => *, Either]:
      override def bimap[A, X, B, Y](l: A => X, r: B => Y): Either[A, B] => Either[X, Y] =
        _.fold(x => l(x).asLeft, x => r(x).asRight)

}

object ExobifunctorHelpers:
  

end ExobifunctorHelpers
