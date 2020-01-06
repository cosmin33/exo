package io.cosmo.exo.categories.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.estatico.newtype.Coercible

trait Exobifunctor[==>[_, _], -->[_, _], ~~>[_, _], Bi[_, _]] {
  type TCL[_]
  def L : Subcat.Aux[==>, TCL]

  type TCR[_]
  def R : Subcat.Aux[-->, TCR]

  type TC[_]
  def C : Subcat.Aux[~~>, TC]

  def bimap[A, X, B, Y](left: A ==> X, right: B --> Y): Bi[A, B] ~~> Bi[X, Y]
// TODO: see how to not need typeclasses (TCR / TCL) for these:
  def leftMap [A, B, Z](fn: A ==> Z): Bi[A, B] ~~> Bi[Z, B] = ??? //bimap(fn, R.id[B])
  def rightMap[A, B, Z](fn: B --> Z): Bi[A, B] ~~> Bi[A, Z] = ??? //bimap(L.id[A], fn)
}

object Exobifunctor extends ExobifunctorInstances {
  type Aux[|=>[_, _], =>#[_], -->[_, _], ->#[_], ~~>[_, _], ~>#[_], ⊙[_, _]] =
    Exobifunctor[|=>, -->, ~~>, ⊙] {type TCL[a] = =>#[a]; type TCR[a] = ->#[a]; type TC[a] = ~>#[a]}
  type AuxTF[⊙[_, _]] = Aux[* => *, Trivial.T1, * => *, Trivial.T1, * => *, Trivial.T1, ⊙]
  type ProTF[⊙[_, _]] = Aux[Dual[* => *,*,*], Trivial.T1, * => *, Trivial.T1, * => *, Trivial.T1, ⊙]

  implicit def coercible[->[_,_], ->#[_], P[_,_], R[_,_]](implicit co: Coercible[∀∀[P], ∀∀[R]])
  : Coercible[Endobifunctor.Aux[->, ->#, P], Endobifunctor.Aux[->, ->#, R]] = Coercible.instance

  implicit def impCoerce[->[_,_], ->#[_], P[_,_], R[_,_]](implicit
    ev: Coercible[Endobifunctor.Aux[->, ->#, P], Endobifunctor.Aux[->, ->#, R]],
    E: Endobifunctor.Aux[->, ->#, P],
  ): Endobifunctor.Aux[->, ->#, R] = ev(E)

  def apply[==>[_, _], =>#[_], -->[_, _], ->#[_], ~~>:[_, _], ~>#[_], ⊙[_, _]](implicit
    bi: Exobifunctor.Aux[==>, =>#, -->, ->#, ~~>:, ~>#, ⊙]
  ): Exobifunctor.Aux[==>, =>#, -->, ->#, ~~>:, ~>#, ⊙] = bi

  trait Proto[|=>[_, _], =>#[_], -->[_, _], ->#[_], ~~>[_, _], ~>#[_], ⊙[_, _]] extends
    Exobifunctor[|=>, -->, ~~>, ⊙] {type TCL[a] = =>#[a]; type TCR[a] = ->#[a]; type TC[a] = ~>#[a]}

}

object Endobifunctor {
  type Aux[->[_, _], ->#[_], ⊙[_, _]] = Exobifunctor.Aux[->, ->#, ->, ->#, ->, ->#, ⊙]
  type AuxT[->[_, _], ⊙[_, _]] = Aux[->, Trivial.T1, ⊙]
  type Proto[->[_, _], TC[_], ⊙[_, _]] = Exobifunctor.Proto[->, TC, ->, TC, ->, TC, ⊙]
}

trait ExobifunctorInstances {

  /**
   * (endo)Endobifunctor is equal to the same Endobifunctor of the opposite category. I don't know hot to prove that
   *   as to obtain a leibniz so I'll just derive it for now...
   */
  def oppEndobifunctor[->[_, _], TC[_], Bi[_, _]](implicit
    c: Subcat.Aux[->, TC],
    source: Endobifunctor.Aux[->, TC, Bi],
  ): Endobifunctor.Aux[Opp[->]#l, TC, Bi] = new Endobifunctor.Proto[Opp[->]#l, TC, Bi] {
    val L, R, C = Subcat.oppCategory(c)
    override def bimap[LX, LY, RX, RY](left: LY -> LX, right: RY -> RX): Bi[LY, RY] -> Bi[LX, RX] =
      source.bimap[LY, LX, RY, RX](left, right)
  }
  implicit def dualEndobifunctor[->[_, _], TC[_], Bi[_, _]](implicit
    c: Subcat.Aux[->, TC],
    source: Endobifunctor.Aux[->, TC, Bi],
  ): Endobifunctor.Aux[Dual[->,*,*], TC, Bi] =
    Dual.leibniz[->].subst[Endobifunctor.Aux[*[_,_], TC, Bi]](oppEndobifunctor[->, TC, Bi])

  implicit def tuple2Endobifunctor: Endobifunctor.Aux[* => *, Trivial.T1, Tuple2] =
    new Endobifunctor.Proto[* => *, Trivial.T1, Tuple2] {
      val L, R, C = Subcat[* => *]
      override def bimap[A, X, B, Y](left: A => X, right: B => Y): ((A, B)) => (X, Y) =
        { case (a, b) => (left(a), right(b)) }
    }

  def tuple2OppEndobifunctor: Endobifunctor.Aux[Opp[* => *]#l, Trivial.T1, Tuple2] =
    oppEndobifunctor[* => *, Trivial.T1, Tuple2](Subcat[* => *], tuple2Endobifunctor)
  def tuple2DualEndobifunctor: Endobifunctor.Aux[Dual[* => *,*,*], Trivial.T1, Tuple2] =
    dualEndobifunctor[* => *, Trivial.T1, Tuple2](Subcat[* => *], tuple2Endobifunctor)

  implicit def eitherEndoBifunctor: Endobifunctor.Aux[* => *, Trivial.T1, Either] =
    new Endobifunctor.Proto[* => *, Trivial.T1, Either] {
      override val L, R, C = Subcat[* => *]
      override def bimap[LX, LY, RX, RY](lxy: LX => LY, rxy: RX => RY): Either[LX, RX] => Either[LY, RY] =
        _.fold(x => Left [LY, RY](lxy(x)), x => Right[LY, RY](rxy(x)))
    }

  def eitherDualEndoBifunctor: Endobifunctor.Aux[Dual[* => *,*,*], Trivial.T1, Either] =
    dualEndobifunctor[* => *, Trivial.T1, Either](Subcat[* => *], eitherEndoBifunctor)

  def eitherOppEndoBifunctor: Endobifunctor.Aux[Opp[* => *]#l, Trivial.T1, Either] =
    oppEndobifunctor[* => *, Trivial.T1, Either](Subcat[* => *], eitherEndoBifunctor)

}
