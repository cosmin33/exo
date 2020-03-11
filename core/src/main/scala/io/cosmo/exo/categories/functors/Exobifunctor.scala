package io.cosmo.exo.categories.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.estatico.newtype.Coercible
import cats.implicits._
import cats.syntax._

trait Exobifunctor[=>:[_, _], ->:[_, _], ~>:[_, _], Bi[_, _]] {
//  type TCL[_]
//  def L : Subcat.Aux[=>:, TCL]
  def L : Semicategory[=>:]

//  type TCR[_]
//  def R : Subcat.Aux[->:, TCR]
  def R : Semicategory[->:]

//  type TC[_]
//  def C : Subcat.Aux[~>:, TC]
  def C : Semicategory[~>:]

  def bimap[A, X, B, Y](left: A =>: X, right: B ->: Y): Bi[A, B] ~>: Bi[X, Y] =
      C.andThen(leftMap[A, B, X](left), rightMap[X, B, Y](right))

  def leftMap [A, B, Z](fn: A =>: Z): Bi[A, B] ~>: Bi[Z, B] //bimap(fn, R.id[B])
  def rightMap[A, B, Z](fn: B ->: Z): Bi[A, B] ~>: Bi[A, Z] //bimap(L.id[A], fn)
}

object Exobifunctor extends ExobifunctorInstances {

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

trait ExobifunctorInstances {

  /**
   * (endo)Endobifunctor is equal to the same Endobifunctor of the opposite category. I don't know hot to prove that
   *   as to obtain a leibniz so I'll just derive it for now...
   */
  def oppEndobifunctor[->[_, _], Bi[_, _]](implicit
    c: Semicategory[->],
    source: Endobifunctor[->, Bi],
  ): Endobifunctor[Opp[->]#l, Bi] = new Endobifunctor[Opp[->]#l, Bi] {
    val L, R, C = Semicategory.oppSemicategory(c)
    override def bimap[LX, LY, RX, RY](left: LY -> LX, right: RY -> RX): Bi[LY, RY] -> Bi[LX, RX] =
      source.bimap[LY, LX, RY, RX](left, right)
    def leftMap [A, B, Z](fn: Z -> A): Bi[Z, B] -> Bi[A, B] = source.leftMap(fn)
    def rightMap[A, B, Z](fn: Z -> B): Bi[A, Z] -> Bi[A, B] = source.rightMap(fn)
  }
  implicit def dualEndobifunctor[->[_, _], Bi[_, _]](implicit
    c: Semicategory[->],
    source: Endobifunctor[->, Bi],
  ): Endobifunctor[Dual[->,*,*], Bi] =
    Dual.leibniz[->].subst[Endobifunctor[*[_,_], Bi]](oppEndobifunctor[->, Bi])

  implicit def tuple2Endobifunctor: Endobifunctor[* => *, Tuple2] =
    new Endobifunctor[* => *, Tuple2] {
      val L, R, C = Semicategory[* => *]
      override def bimap[A, X, B, Y](left: A => X, right: B => Y): ((A, B)) => (X, Y) =
        { case (a, b) => (left(a), right(b)) }
      def leftMap [A, B, Z](fn: A => Z): ((A, B)) => (Z, B) = { case (a, b) => (fn(a), b) }
      def rightMap[A, B, Z](fn: B => Z): ((A, B)) => (A, Z) = { case (a, b) => (a, fn(b)) }
    }

  def tuple2OppEndobifunctor: Endobifunctor[Opp[* => *]#l, Tuple2] =
    oppEndobifunctor[* => *, Tuple2](Semicategory[* => *], tuple2Endobifunctor)
  def tuple2DualEndobifunctor: Endobifunctor[Dual[* => *,*,*], Tuple2] =
    dualEndobifunctor[* => *, Tuple2](Subcat[* => *], tuple2Endobifunctor)

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

  def eitherDualEndoBifunctor: Endobifunctor[Dual[* => *,*,*], Either] =
    dualEndobifunctor[* => *, Either](Semicategory[* => *], eitherEndoBifunctor)

  def eitherOppEndoBifunctor: Endobifunctor[Opp[* => *]#l, Either] =
    oppEndobifunctor[* => *, Either](Semicategory[* => *], eitherEndoBifunctor)

}
