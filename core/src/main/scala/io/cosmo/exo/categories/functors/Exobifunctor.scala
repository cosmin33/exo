package io.cosmo.exo.categories.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.estatico.newtype.Coercible
import cats.implicits._
import cats.syntax._
import mouse.any._

trait Exobifunctor[==>[_, _], -->[_, _], >->[_, _], Bi[_, _]] { self =>
  def L : Semicategory[==>]
  def R : Semicategory[-->]
  def C : Semicategory[>->]

  def bimap[A, X, B, Y](left: A ==> X, right: B --> Y): Bi[A, B] >-> Bi[X, Y] =
      C.andThen(leftMap[A, B, X](left), rightMap[X, B, Y](right))

  def leftMap [A, B, Z](fn: A ==> Z): Bi[A, B] >-> Bi[Z, B] //bimap(fn, R.id[B])
  def rightMap[A, B, Z](fn: B --> Z): Bi[A, B] >-> Bi[A, Z] //bimap(L.id[A], fn)

}

object Exobifunctor extends ExobifunctorInstances {

  type EndoPro[->[_,_], B[_,_]] = Exobifunctor[Dual[->,*,*], ->, ->, B]
  type Endo[->[_,_], B[_,_]] = Exobifunctor[->, ->, ->, B]

  implicit class ExobifunctorOps[==>[_,_], >->[_,_], F[_,_]](val self: Exobifunctor[==>, ==>, >->, F]) extends AnyVal {
    def compose[G[_,_]](G: Exobifunctor[==>, ==>, ==>, G]): Exobifunctor[==>, ==>, >->, λ[(α, β) => F[G[α, β], G[α, β]]]] =
      new Exobifunctor[==>, ==>, >->, λ[(α, β) => F[G[α, β], G[α, β]]]] {
        val L = self.L
        val R = self.R
        val C = self.C
        override def bimap[A, X, B, Y](left: A ==> X, right: B ==> Y) = G.bimap(left, right) |> (i => self.bimap(i, i))
        def leftMap [A, B, Z](fn: A ==> Z) = G.leftMap (fn) |> ((i: G[A, B] ==> G[Z, B]) => self.bimap(i, i))
        def rightMap[A, B, Z](fn: B ==> Z) = G.rightMap(fn) |> ((i: G[A, B] ==> G[A, Z]) => self.bimap(i, i))
      }
  }

  implicit def coercible[->[_,_], P[_,_], R[_,_]](implicit co: Coercible[∀∀[P], ∀∀[R]])
  : Coercible[Endobifunctor[->, P], Endobifunctor[->, R]] = Coercible.instance

  implicit def impCoerce[->[_,_], P[_,_], R[_,_]](implicit
    ev: Coercible[Endobifunctor[->, P], Endobifunctor[->, R]],
    E: Endobifunctor[->, P],
  ): Endobifunctor[->, R] = ev(E)

  def apply[=>:[_, _], ->:[_, _], ~>:[_, _], ⊙[_, _]](implicit
    bi: Exobifunctor[=>:, ->:, ~>:, ⊙]
  ): Exobifunctor[=>:, ->:, ~>:, ⊙] = bi

  type Pro[->[_,_]] = Exobifunctor[Opp[* => *]#l, * => *, * => *, ->]

}

object Endobifunctor {
  def apply[->[_,_], Bi[_,_]](implicit e: Endobifunctor[->, Bi]): Endobifunctor[->, Bi] = e
}

trait ExobifunctorInstances {

  implicit def dicatToIso[==>[_, _], -->[_, _], >->[_, _], Bi[_, _], TC[_]](
    E: Exobifunctor[Dicat[==>,*,*], Dicat[-->,*,*], >->, Bi]
  )(implicit
    S1: Subcat.Aux[==>, TC],
    S2: Subcat.Aux[-->, TC],
  ): Exobifunctor[Iso[==>,*,*], Iso[-->,*,*], >->, Bi] =
    new Exobifunctor[Iso[==>,*,*], Iso[-->,*,*], >->, Bi] {
      def L = Iso.isoGroupoid(S1)
      def R = Iso.isoGroupoid(S2)
      def C = E.C
      def leftMap [A, B, Z](fn: Iso[==>, A, Z]) = E.leftMap (Dicat[==>, A, Z](fn.to, fn.from))
      def rightMap[A, B, Z](fn: Iso[-->, B, Z]) = E.rightMap(Dicat[-->, B, Z](fn.to, fn.from))
    }

  implicit def tuple2Endobifunctor: Endobifunctor[* => *, Tuple2] =
    new Endobifunctor[* => *, Tuple2] {
      val L, R, C = Semicategory[* => *]
      override def bimap[A, X, B, Y](left: A => X, right: B => Y): ((A, B)) => (X, Y) =
        { case (a, b) => (left(a), right(b)) }
      def leftMap [A, B, Z](fn: A => Z): ((A, B)) => (Z, B) = { case (a, b) => (fn(a), b) }
      def rightMap[A, B, Z](fn: B => Z): ((A, B)) => (A, Z) = { case (a, b) => (a, fn(b)) }
    }

  implicit def eitherEndoBifunctor: Endobifunctor[* => *, Either] =
    new Endobifunctor[* => *, Either] {
      override val L, R, C = Semicategory[* => *]
      override def bimap[LX, LY, RX, RY](lxy: LX => LY, rxy: RX => RY): Either[LX, RX] => Either[LY, RY] =
        _.fold(x => lxy(x).asLeft, x => rxy(x).asRight)
      def leftMap [A, B, Z](fn: A => Z): Either[A, B] => Either[Z, B] =
        _.fold(a => fn(a).asLeft, b => b.asRight)
      def rightMap[A, B, Z](fn: B => Z): Either[A, B] => Either[A, Z] =
        _.fold(a => a.asLeft, b => fn(b).asRight)
    }

}
