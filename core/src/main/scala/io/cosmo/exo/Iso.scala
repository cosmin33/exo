package io.cosmo.exo

import io.cosmo.exo.Iso.HasIso
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.Exo
import io.cosmo.exo.evidence.{=:!=, =~~=}
import io.cosmo.exo.internalstuff.TupleGeneric
import io.cosmo.exo.typeclasses.{HasTc, TypeF}
import io.estatico.newtype.macros.newtype
import shapeless.Generic

trait Iso[->[_,_], A, B] { ab =>
  def cat: Subcat[->]
  def to:   A -> B
  def from: B -> A

  private type <->[X, Y] = Iso[->, X, Y]

  final def apply(a: A)(implicit ev: =~~=[->, * => *]): B = ev(to)(a)

  final def andThen[C](bc: B <-> C): A <-> C =
    Iso.unsafe(cat.andThen(ab.to, bc.to), cat.andThen(bc.from, ab.from))(cat)

  final def compose[Z](za: Z <-> A): Z <-> B = za.andThen(ab)

  /** Flips the isomorphism from A <-> B to B <-> A grace to it's reflexivity property */
  def flip: B <-> A = new (B <-> A) {
    val (cat, to, from) = (ab.cat, ab.from, ab.to)
    override val flip = ab
  }

  /** If A <-> B then having a function B -> B we can obtain A -> A */
  def teleport(f: A -> A)(implicit C: Semicategory[->]): B -> B = C.andThen(ab.from, C.andThen(f, ab.to))

  /** Having A <-> B searches implicits for B <-> C to obtain A <-> C */
  def chain[C](implicit i: HasIso[->, B, C]): A <-> C = ab.andThen(i)

  /** Having F <~> G searches implicits for G <~> H to obtain F <~> H */
  def chainK[C[_]](implicit i: HasIso[->, B, TypeF[C]]): A <-> TypeF[C] = ab.andThen(i)

  /** For some invariant F[_] if we have an F[A] we can obtain an F[B] using A <-> B */
  def derive[F[_]](implicit fa: F[A], I: Exo.IsoFun[->, F]): F[B] = I.map(ab)(fa)

  /** Typeclass derivation: having TypeF[F] <-> TypeF[G] we can obtain HasTc[TC, A] => HasTc[TC, B] */
  def deriveK[TC[_[_]]](implicit tc: HasTc[TC, A], E: Exo.IsoFun[->, HasTc[TC, *]]): HasTc[TC, B] = E.map(ab)(tc)

  /** From A <-> B, X <-> Y we can obtain (A ⨂ X) <-> (B ⨂ Y) if -> has a Cartesian instance with ⨂ */
  def and[⨂[_,_]] = new AndPartial[⨂]
  class AndPartial[⨂[_,_]] {
    def apply[I, J](ij: I <-> J)(implicit C: Cartesian[->, ⨂]): ⨂[A, I] <-> ⨂[B, J] =
      Iso.unsafe(C.split(ab.to, ij.to), C.split(ab.from, ij.from))(C.C)
  }

  /** From A <-> B, X <-> Y we can obtain (A, X) <-> (B, Y) if -> has a Cartesian instance with Tuple2 */
  def and_[I, J](ij: I <-> J)(implicit C: Cartesian[->, Tuple2]): (A, I) <-> (B, J) = and[Tuple2](ij)

  /** From A <-> B, X <-> Y we can obtain (A ⨁ X) <-> (B ⨁ Y) if -> has a Cocartesian instance with ⨁ */
  def or[⨁[_,_]] = new OrPartial[⨁]
  class OrPartial[⨁[_,_]] {
    def apply[I, J](ij: I <-> J)(implicit C: Cocartesian[->, ⨁]): ⨁[A, I] <-> ⨁[B, J] =
      Iso.unsafe[->, ⨁[A, I], ⨁[B, J]](C.split(Dual(ab.to), Dual(ij.to)), C.split(Dual(ab.from), Dual(ij.from)))(ab.cat)
  }

  /** From A <-> B, X <-> Y we can obtain (A \/ X) <-> (B \/ Y) if -> has a Cocartesian instance with \/ */
  def or_[I, J](ij: I <-> J)(implicit C: Cocartesian[->, \/]): (A \/ I) <-> (B \/ J) = or[\/](ij)

}

object Iso extends IsoInstances {
  def apply[->[_,_], A, B](implicit iso: Iso[->, A, B]): Iso[->, A, B] = iso

  def liftFnToIso[==>[_,_], -->[_,_]](iso: ==> <~~> -->)(implicit
    c1: Subcat[==>], c2: Subcat[-->]
  ): Iso[==>,*,*] <~~> Iso[-->,*,*] =
    <~~>.unsafe(
      ∀∀.mk[Iso[==>,*,*] ~~> Iso[-->,*,*]].from(i => Iso.unsafe(iso.to.exec(i.to),   iso.to.exec(i.from))),
      ∀∀.mk[Iso[-->,*,*] ~~> Iso[==>,*,*]].from(i => Iso.unsafe(iso.from.exec(i.to), iso.from.exec(i.from)))
    )

  private val reflAny: Iso[* => *, Any, Any] =
    new Iso[* => *, Any, Any] {
      type TC[a] = Trivial.T1[a]
      val cat = Subcat[* => *]
      val to, from = identity[Any]
    }

  def refl[A]: Iso[* => *, A, A] = reflAny.asInstanceOf[Iso[* => *, A, A]]

  def apply[A]: Iso[* => *, A, A] = refl[A]

  def refl[->[_,_], A, TC[_]](implicit c: Subcat.Aux[->, TC], tc: TC[A]): Iso[->, A, A] =
    new Iso[->, A, A] {val cat = c; val to, from = c.id[A]}

  /** create an isomorphism given the two complementary functions as long as you promise to uphold the iso laws */
  def unsafe[->[_,_], A, B](ab: A -> B, ba: B -> A)(implicit C: Subcat[->]): Iso[->, A, B] =
    new Iso[->, A, B] {val (cat, to, from) = (C, ab, ba)}
  //def unsafe[->[_,_], A, B](pair: (A -> B, B -> A))(implicit C: Subcat[->]): Iso[->, A, B] = unsafe(pair._1, pair._2)

  /** Isomorphism between a case class and a tuple of the proper arity (using shapeless) */
  def forCaseClass[S <: Product](implicit ev: TupleGeneric[S]): Iso[* => *, S, ev.Repr] =
    Iso.unsafe(s => ev.to(s), t => ev.from(t))

  /** Isomorphism between a case class and it's generic representation (from shapeless) */
  def forGeneric[A, Repr](implicit g: Generic.Aux[A, Repr]): A <=> Repr = Iso.unsafe(g.to, g.from)

  /** Isomorphism between any iso and it's flipped iso */
  def flippedIso[->[_,_], A, B]: Iso[->, A, B] <=> Iso[->, B, A] = Iso.unsafe(_.flip, _.flip)

  /** Isomorphism between an iso and a tuple of 'to' and 'from' functions */
  def isoIsoTuple[->[_,_]: Subcat, A, B]: Iso[->, A, B] <=> (A -> B, B -> A) =
    Iso.unsafe(i => (i.to, i.from), t => Iso.unsafe(t._1, t._2))

  /** Any singleton is isomorphic with unit */
  implicit def isoUnitSingleton[A <: Singleton](implicit
    a: ValueOf[A]
  ): A <=> Unit = Iso.unsafe((_: A) => (), (_: Unit) => a.value)

  /** Any two singletons are isomorphic */
  implicit def isoBetweenSingletons[A <: Singleton, B <: Singleton](implicit
    a: ValueOf[A], b: ValueOf[B], neq: A =:!= B
  ): A <=> B = Iso.unsafe((_: A) => b.value, (_: B) => a.value)

  def isoUnitToA[A]:     (Unit => A) <=> A         = Iso.unsafe(_(()), a => _ => a)
  def isoAToUnit[A]:     (A => Unit) <=> Unit      = Iso.unsafe(_ => (), _ => _ => ())
  def isoVoidToA[A]:   (Void => A) <=> Unit      = Iso.unsafe(_ => (), _ => a => a)
  def isoVoidUnit[A, B]: (A => Unit) <=> (Void => B) = Iso.unsafe(_ => v => v, _ => _ => ())

  def isoTerminalInitial[->[_,_], T, I, A, TC[_]](implicit
    T: HasTerminalObject.Aux[->, TC, T],
    I: HasInitialObject.Aux[->, TC, I],
    TC: TC[A]
  ): (A -> T) <=> (I -> A) = Iso.unsafe(_ => I.initiate, _ => T.terminate)

  def isoTerminalUnit[->[_,_], T, A, TC[_]](implicit
    cat: Subcat.Aux[->, TC],
    T: HasTerminalObject.Aux[->, TC, T],
    tca: TC[A],
  ): (A -> T) <=> (T -> T) = Iso.unsafe(_ => cat.id[T](T.terminal), _ => T.terminate)

  def isoInitialUnit[->[_,_], I, A, TC[_]](implicit
    cat: Subcat.Aux[->, TC],
    I: HasInitialObject.Aux[->, TC, I],
    tca: TC[A],
  ): (I -> A) <=> (I -> I) = Iso.unsafe(_ => cat.id[I](I.initial), _ => I.initiate)

  object Product {
    final def associate[A, B, C]: (A, (B, C)) <=> ((A, B), C) = Iso.unsafe({
      case (a, (b, c)) => ((a, b), c) }, { case ((a, b), c) => (a, (b, c)) })
    final def commute[A, B]: (A, B) <=> (B, A) = unsafe({ case (a, b) => (b, a) }, { case (b, a) => (a, b) })
    final def unitL[A]: A <=> (Unit, A) = unsafe(a => ((), a), { case ((), a) => a })
    final def unitR[A]: A <=> (A, Unit) = unsafe(a => (a, ()), { case (a, ()) => a })
    final def first [A, B, C](iso: A <=> C): (A, B) <=> (C, B) = iso.and(refl[B])(Associative.cartesianFn1Tuple)
    final def second[A, B, C](iso: B <=> C): (A, B) <=> (A, C) = refl[A].and(iso)(Associative.cartesianFn1Tuple)
  }

  object Coproduct {
    final def associate[A, B, C]: (A \/ (B \/ C)) <=> ((A \/ B) \/ C) =
      Iso.unsafe(
        _.fold(a => -\/(-\/(a)), _.fold(b => -\/(\/-(b)), c => \/-(c))),
        _.fold(_.fold(a => -\/(a), b => \/-(-\/(b))), c => \/-(\/-(c)))
      )
    final def commute[A, B]: (A \/ B) <=> (B \/ A) = unsafe((e: A \/ B) => e.swap, (e: B \/ A) => e.swap)
    final def unitL[A]: A <=> (Void \/ A) = unsafe(a => \/-(a), _.fold((n: A) => n, identity))
    final def unitR[A]: A <=> (A \/ Void) = unsafe(a => -\/(a), _.fold(identity, (n: A) => n))
    final def first [A, B, C](iso: A <=> C): (A \/ B) <=> (C \/ B) = iso.or_(refl[B])(Associative.cocartesianFn1DisjDual)
    final def second[A, B, C](iso: B <=> C): (A \/ B) <=> (A \/ C) = refl[A].or_(iso)(Associative.cocartesianFn1DisjDual)
  }

//  @newtype case class HasIso1[->[_,_], A, B](iso: Iso[->, A, B])
//  object HasIso1 {
//    implicit def hi1[->[_,_], A, B](implicit
//      imps: ((A === B) /\ Subcat.Triv[->])
//        \/ Iso[->, A, B]
//        \/ Iso[->, B, A],
//    ): HasIso1[->, A, B] = {
//      imps.fold3(
//        i => HasIso1(i._1.subst[Iso[->, A, *]](Iso.refl[->, A, Trivial.T1](i._2.subcat, implicitly))),
//        i => HasIso1(i),
//        i => HasIso1(i.flip)
//      )
//    }
//  }

  @newtype case class HasIso[->[_,_], A, B](iso: Iso[->, A, B])
  object HasIso {
    implicit def conversionToIso[->[_, _], A, B](hi: HasIso[->, A, B]): Iso[->, A, B] = hi.iso

    implicit def hasIsoImpRefl[->[_,_], A, T[_]](implicit s: Subcat.Aux[->, T], t: T[A]): HasIso[->, A, A] =
      HasIso(Iso.refl[->, A, T])
    implicit def hasIsoImpAB[->[_,_], A: * =:!= B, B](implicit i: Iso[->, A, B]): HasIso[->, A, B] = HasIso(i)
    implicit def hasIsoImpBA[->[_,_], A: * =:!= B, B](implicit i: Iso[->, B, A]): HasIso[->, A, B] = HasIso(i.flip)
  }

  object syntax extends IsoSyntax
}

trait IsoSyntax {
  implicit def toIsoOps[A](self: A): IsoSyntaxOps[A] = new IsoSyntaxOps(self)
  implicit def toIsokOps[F[_]](self: TypeF[F]): IsokSyntaxOps[F] = new IsokSyntaxOps(self)
}

final class IsokSyntaxOps[F[_]](val self: TypeF[F]) extends AnyVal {
  def isoWith[G[_]](implicit h: HasIso[FunK, TypeF[F], TypeF[G]]): F <~> G = FunK.isoKIso(h.iso)
}
final class IsoSyntaxOps[A](val self: A) extends AnyVal {
  def isoTo[B](implicit h: Iso.HasIso[* => *, A, B]): B = h(self)
}

import io.cosmo.exo.IsoHelperTraits._

trait IsoInstances extends IsoInstances1 {
  implicit def isoBifunctor[->[_,_], ->#[_], ⊙[_,_]](implicit
    S: Subcat.Aux[->, ->#], B: Endobifunctor[->, ⊙],
  ): Endobifunctor[Iso[->, *, *], ⊙] =
    new IsoBifunctor[->, ->#, ⊙] {val cat = S; val bif = B; val L, R, C = Iso.isoGroupoid(S)}

  implicit def isoGroupoid[->[_,_], T[_]](implicit C: Subcat.Aux[->, T]
  ): Groupoid.Aux[Iso[->, *, *], T] = new IsoGroupoid[->, T] {val cat = C}

  implicit def isoAssoc[->[_,_], ⊙[_,_], T[_]](implicit
    a: Associative.Aux[->, ⊙, T],
    b: Endobifunctor[->, ⊙],
  ): Associative.Aux[Iso[->, *, *], ⊙, T] = new IsoAssoc[->, T, ⊙] {val A = a; val bif = b}
}
trait IsoInstances1 extends IsoInstances2 {
  implicit def isoBraided[->[_,_], ⊙[_,_], T[_]](implicit
    a: Braided.Aux[->, ⊙, T],
    b: Endobifunctor[->, ⊙],
  ): Braided.Aux[Iso[->, *, *], ⊙, T] = new IsoBraided[->, ⊙, T] {val A = a; val bif = b}

  implicit def isoMonoidal[->[_,_], ⊙[_,_], T[_], I](implicit
    a: Monoidal.Aux[->, ⊙, T, I],
    b: Endobifunctor[->, ⊙],
  ): Monoidal.Aux[Iso[->, *, *], ⊙, T, I] = new IsoMonoidal[->, ⊙, T, I] {val A = a; val bif = b}
}
trait IsoInstances2 {
  implicit def isoSymmetric[->[_,_], ⊙[_,_], T[_]](implicit
    a: Symmetric.Aux[->, ⊙, T],
    b: Endobifunctor[->, ⊙],
  ): Symmetric.Aux[Iso[->, *, *], ⊙, T] = new IsoSymmetric[->, ⊙, T] {val A = a; val bif = b}
}

private[exo] object IsoHelperTraits {

  trait IsoBifunctor[->[_,_], ->#[_], ⊙[_,_]] extends Endobifunctor[Iso[->,*,*], ⊙] {
    def cat: Subcat.Aux[->, ->#]
    def bif: Endobifunctor[->, ⊙]
    private type <->[a,b] = Iso[->, a, b]
    override def bimap[A, X, B, Y](l: A <-> X, r: B <-> Y): ⊙[A, B] <-> ⊙[X, Y] =
      Iso.unsafe(bif.bimap(l.to, r.to), bif.bimap(l.from, r.from))(cat)
    def leftMap [A, B, Z](fn: A <-> Z): ⊙[A, B] <-> ⊙[Z, B] = Iso.unsafe(bif.leftMap[A, B, Z](fn.to), bif.leftMap[Z, B, A](fn.from))(cat)
    def rightMap[A, B, Z](fn: B <-> Z): ⊙[A, B] <-> ⊙[A, Z] = Iso.unsafe(bif.rightMap[A, B, Z](fn.to), bif.rightMap[A, Z, B](fn.from))(cat)
  }

  trait IsoGroupoid[->[_,_], T[_]] extends Groupoid[Iso[->, *, *]] {
    def cat: Subcat.Aux[->, T]
    type TC[a] = T[a]
    def id[A](implicit A: T[A]): Iso[->, A, A] = Iso.refl[->, A, TC](cat, A)

    def flip[A, B](f: Iso[->, A, B]): Iso[->, B, A] = f.flip

    def andThen[A, B, C](ab: Iso[->, A, B], bc: Iso[->, B, C]): Iso[->, A, C] = ab.andThen(bc)
  }

  trait IsoAssoc[->[_,_], T[_], ⊙[_,_]] extends Associative[Iso[->, *, *], ⊙] {
    def A: Associative.Aux[->, ⊙, T]
    def bif: Endobifunctor[->, ⊙]
    type TC[a] = T[a]
    def C = Iso.isoGroupoid(A.C)
    def bifunctor = Iso.isoBifunctor(A.C, bif)
    def associate[X, Y, Z]  : Iso[->, X ⊙ Y ⊙ Z, X ⊙ (Y ⊙ Z)] = Iso.unsafe(A.associate[X, Y, Z], A.diassociate[X, Y, Z])(A.C)
    def diassociate[X, Y, Z]: Iso[->, X ⊙ (Y ⊙ Z), X ⊙ Y ⊙ Z] = Iso.unsafe(A.diassociate[X, Y, Z], A.associate[X, Y, Z])(A.C)
  }

  trait IsoBraided[->[_,_], ⊙[_,_], T[_]] extends Braided[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    def A: Braided.Aux[->, ⊙, T]
    def braid[A, B]: Iso[->, A ⊙ B, B ⊙ A] = Iso.unsafe(A.braid[A, B], A.braid[B, A])(A.C)
  }

  trait IsoSymmetric[->[_,_], ⊙[_,_], T[_]] extends Symmetric[Iso[->, *, *], ⊙] with IsoBraided[->, ⊙, T] {
    def A: Symmetric.Aux[->, ⊙, T]
  }

  trait IsoMonoidal[->[_,_], ⊙[_,_], T[_], I] extends Monoidal[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    def A: Monoidal.Aux[->, ⊙, T, I]
    type Id = I
    def idl[A]:   Iso[->, I ⊙ A, A  ] = Iso.unsafe(A.idl[A], A.coidl[A])(A.C)
    def coidl[A]: Iso[->,   A, I ⊙ A] = Iso.unsafe(A.coidl[A], A.idl[A])(A.C)
    def idr[A]:   Iso[->, A ⊙ I, A  ] = Iso.unsafe(A.idr[A], A.coidr[A])(A.C)
    def coidr[A]: Iso[->,   A, A ⊙ I] = Iso.unsafe(A.coidr[A], A.idr[A])(A.C)
  }

}
