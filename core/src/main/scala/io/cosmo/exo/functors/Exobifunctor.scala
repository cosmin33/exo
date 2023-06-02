package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._
import io.cosmo.exo.internal._

trait Exobifunctor[==>[_, _], -->[_, _], >->[_, _], ⊙[_, _]] { self =>
  def bimap[A, X, B, Y](left: A ==> X, right: B --> Y): ⊙[A, B] >-> ⊙[X, Y]

  def leftMap [A, B, Z](fn: A ==> Z)(implicit C: SubcatHasId[-->, B]): ⊙[A, B] >-> ⊙[Z, B] = bimap(fn, C.id)
  def rightMap[A, B, Z](fn: B --> Z)(implicit C: SubcatHasId[==>, A]): ⊙[A, B] >-> ⊙[A, Z] = bimap(C.id, fn)

  def leftFunctor [X](implicit C: SubcatHasId[-->, X]): Exo[==>, >->, ⊙[*, X]] =
    Exo.unsafe[==>, >->, ⊙[*, X]]([a, b] => (fn: a ==> b) => leftMap(fn))
  def rightFunctor[X](implicit C: SubcatHasId[==>, X]): Exo[-->, >->, ⊙[X, *]] =
    Exo.unsafe[-->, >->, ⊙[X, *]]([a, b] => (fn: a --> b) => rightMap(fn))

  def leftForall [T[_]](implicit C: Subcat.Aux[-->, T]): T ~> ([x] =>> Exo[==>, >->, ⊙[*, x]]) =
    [A] => (ta: T[A]) => leftFunctor(SubcatHasId.from(using C, ta))
  def rightForall[T[_]](implicit C: Subcat.Aux[==>, T]): T ~> ([x] =>> Exo[-->, >->, ⊙[x, *]]) =
    [A] => (ta: T[A]) => rightFunctor(SubcatHasId.from(using C, ta))

}

object Exobifunctor extends ExobifunctorInstances with DualBifunctorInstances {

  type EndoPro[->[_,_], B[_,_]] = Exobifunctor[Dual[->,*,*], ->, ->, B]
  type Endo[->[_,_], B[_,_]] = Exobifunctor[->, ->, ->, B]
  type Con[==>[_,_], -->[_,_], >->[_,_], B[_,_]] = Exobifunctor[Dual[==>,*,*], Dual[-->,*,*], >->, B]
  type ConF[B[_,_]] = Con[* => *, * => *, * => *, B]

  def apply[=>:[_,_], ->:[_,_], ~>:[_,_], ⊙[_,_]](using bi: Exobifunctor[=>:, ->:, ~>:, ⊙]): Exobifunctor[=>:, ->:, ~>:, ⊙] = bi

  def fromFaFunctors[==>[_,_], -->[_,_], >->[_,_]: Semicategory, Bi[_,_]](
   L: ∀[[a] =>> Exo[==>, >->, Bi[*, a]]],
   R: ∀[[a] =>> Exo[-->, >->, Bi[a, *]]]
 ): Exobifunctor[==>, -->, >->, Bi] = {
    new Exobifunctor[==>, -->, >->, Bi] {
      def bimap[A, X, B, Y](l: A ==> X, r: B --> Y): Bi[A, B] >-> Bi[X, Y] = ??? //L.apply[B].map(l) >>>> R.apply[X].map(r)
      override def leftMap [A, B, Z](fn:  A ==> Z)(implicit C:  SubcatHasId[-->, B]) = L.apply[B].map(fn)
      override def rightMap[A, B, Z](fn:  B --> Z)(implicit C:  SubcatHasId[==>, A]) = R.apply[A].map(fn)
    }
  }

  implicit class ExobifunctorOps[==>[_,_], >->[_,_], F[_,_]](val self: Exobifunctor[==>, ==>, >->, F]) extends AnyVal {
    def compose[G[_,_]](implicit G: Endobifunctor[==>, G]): Exobifunctor[==>, ==>, >->, λ[(α, β) => F[G[α, β], G[α, β]]]] =
      new Exobifunctor[==>, ==>, >->, λ[(α, β) => F[G[α, β], G[α, β]]]] {
        def bimap[A, X, B, Y](l: A ==> X, r: B ==> Y) = G.bimap(l, r) |> (i => self.bimap(i, i))
      }
  }

  implicit def profunctor[->[_,_]: Semicategory]: Exobifunctor[Dual[->,*,*], ->, * => *, ->] =
    new Exobifunctor[Dual[->,*,*], ->, * => *, ->] {
      def bimap[A, X, B, Y](left: Dual[->, A, X], right: B -> Y): A -> B => (X -> Y) = f => ??? //left.toFn >>>> f >>>> right
    }

  def dual[->[_,_], Bi[_,_]](F: Endobifunctor[->, Bi]): Endobifunctor[Dual[->,*,*], Bi] =
    new Endobifunctor[Dual[->,*,*], Bi] {
      def bimap[A, X, B, Y](l: Dual[->, A, X], r: Dual[->, B, Y]): Dual[->, Bi[A, B], Bi[X, Y]] =
        Dual(F.bimap(l, r))
    }

  def opp[->[_,_], Bi[_,_]](F: Endo[->, Bi]): Endo[Opp[->]#l, Bi] =
    Dual.leibniz[->].flip.subst[[f[_,_]] =>> Endo[f, Bi]](dual(F))
}

object Endobifunctor {
  def apply[->[_,_], Bi[_,_]](using e: Endobifunctor[->, Bi]): Endobifunctor[->, Bi] = e
}

trait ExobifunctorInstances {

  private[exo] def dicatToIso[==>[_, _], -->[_, _], >->[_, _], Bi[_, _], TC[_]](
   E: Exobifunctor[Dicat[==>,*,*], Dicat[-->,*,*], >->, Bi]
 )(implicit
   S1: Subcat.Aux[==>, TC],
   S2: Subcat.Aux[-->, TC],
 ): Exobifunctor[Iso[==>,*,*], Iso[-->,*,*], >->, Bi] =
    new Exobifunctor[Iso[==>,*,*], Iso[-->,*,*], >->, Bi] {
      override def bimap[A, X, B, Y](left: Iso[==>, A, X], right: Iso[-->, B, Y]) =
        E.bimap(Dicat[==>, A, X](left.to, left.from), Dicat[-->, B, Y](right.to, right.from))
    }

  given tuple2: Endobifunctor[* => *, Tuple2] =
    new Endobifunctor[* => *, Tuple2] {
      override def bimap[A, X, B, Y](left: A => X, right: B => Y): ((A, B)) => (X, Y) =
      { case (a, b) => (left(a), right(b)) }
    }

  given either: Endobifunctor[* => *, Either] =
    new Endobifunctor[* => *, Either] {
      override def bimap[LX, LY, RX, RY](lxy: LX => LY, rxy: RX => RY): Either[LX, RX] => Either[LY, RY] =
        _.fold(x => lxy(x).asLeft, x => rxy(x).asRight)
    }

  given semicatToExobifunctor[->[_,_]](using s: Semicategory[->]): Exobifunctor[Dual[->,*,*], ->, Function, ->] =
    new Exobifunctor[Dual[->,*,*], ->, * => *, ->]:
      def bimap[A, X, B, Y](left: Dual[->, A, X], right: B -> Y): (A -> B) => (X -> Y) = left.toFn >>> _ >>> right


}
