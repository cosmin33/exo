package io.cosmo.exo

import io.cosmo.exo.Iso.HasIso
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.data.ProdCat.Dicat
import io.cosmo.exo.categories.functors.{Endobifunctor, Exofunctor}
import io.cosmo.exo.evidence.{=!=, =:!=, =~~=, IsK2}
import io.cosmo.exo.internalstuff.TupleGeneric
import io.cosmo.exo.typeclasses.{HasTc, IsTypeF, TypeF}
import io.estatico.newtype.macros.newtype
import shapeless.{Generic, HList}

trait Iso[->[_,_], A, B] { ab =>
  def cat: Subcat[->]
  def to:   A -> B
  def from: B -> A

  private type <->[X, Y] = Iso[->, X, Y]

  final def apply(a: A)(implicit ev: IsK2[->, * => *]): B = ev(to)(a)

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
  def chainK[C[_]](implicit
    ev: -> =~~= FunK,
    ta: IsTypeF[A],
    tb: IsTypeF[B],
    i: HasIso[->, B, TypeF[C]],
  ): A <-> TypeF[C] = ab.andThen(i)

  /** For some invariant F[_] if we have an F[A] we can obtain an F[B] using A <-> B */
  def derive[F[_]](implicit fa: F[A], I: Exofunctor.InvF[F], eq: -> =~~= Function1): F[B] =
    I.map(Dicat[* => *, A, B](eq(ab.to), eq(ab.from)))(fa)

  def deriveK[TC[_[_]]](implicit
    tc: HasTc[TC, A],
    ta: IsTypeF[A],
    tb: IsTypeF[B],
    I: Exofunctor.Aux[Dicat[FunK, *, *], * => *, HasTc[TC, *], IsTypeF, Trivial.T1],
    eq: -> =~~= FunK,
  ): HasTc[TC, B] = I.map(Dicat(eq(ab.to), eq(ab.from)))(tc)

  /** From A <-> B, X <-> Y we can obtain (A ⨂ X) <-> (B ⨂ Y) if -> has a Cartesian instance with ⨂ */
  def and[I, J, ⨂[_,_]](that: I <-> J)(implicit C: Cartesian[->, ⨂]): ⨂[A, I] <-> ⨂[B, J] =
    Iso.unsafe(C.pair(ab.to, that.to), C.pair(ab.from, that.from))(C.C)

  /** From A <-> B, X <-> Y we can obtain (A ⨁ X) <-> (B ⨁ Y) if -> has a Cocartesian instance with ⨁ */
  def or[I, J, ⨁[_,_]](that: I <-> J)(implicit C: Cocartesian[->, ⨁]): ⨁[A, I] <-> ⨁[B, J] =
    Iso.unsafe(C.pair(ab.to, that.to), C.pair(ab.from, that.from))(ab.cat)
}

object Iso extends IsoInstances {
  def apply[->[_,_], A, B](implicit iso: Iso[->, A, B]): Iso[->, A, B] = iso

  private final class Refl[A]() extends Iso[* => *, A, A] {
    type TC[a] = Trivial.T1[a]
    val cat = implicitly
    val to = identity
    val from = identity
  }
  private val refl_ : ∀[Refl] = ∀.of[Refl](new Refl())

  def refl[A]: Iso[* => *, A, A] = refl_[A]

  def refl[->[_,_], A, Cons[_]](implicit c: Subcat.Aux[->, Cons], cons: Cons[A]): Iso[->, A, A] =
    new Iso[->, A, A] {val cat = c; val to, from = c.id[A]}

  def unsafe[->[_,_], A, B](ab: A -> B, ba: B -> A)(implicit C: Subcat[->]): Iso[->, A, B] =
    new Iso[->, A, B] {val (cat, to, from) = (C, ab, ba)}

  /** Isomorphism between a case class and a tuple of the proper arity (using shapeless) */
  def forCaseClass[S <: Product](implicit ev: TupleGeneric[S]): Iso[* => *, S, ev.Repr] =
    Iso.unsafe(s => ev.to(s), t => ev.from(t))

  /** Isomorphism between a case class and it's generic representation (from shapeless) */
  def forGeneric[A, Repr](implicit g: Generic.Aux[A, Repr]): <=>[A, Repr] = Iso.unsafe(g.to, g.from)

  /** Any singleton is isomorphic with unit */
  implicit def isoUnitSingleton[A <: Singleton](implicit
    a: ValueOf[A]
  ): A <=> Unit = Iso.unsafe((_: A) => (), (_: Unit) => a.value)

  /** Any two singletons are isomorphic */
  implicit def isoBetweenSingletons[A <: Singleton, B <: Singleton](implicit
    a: ValueOf[A], b: ValueOf[B], neq: A =:!= B
  ): A <=> B = Iso.unsafe((_: A) => b.value, (_: B) => a.value)

  def isoUnitToA[A]:     <=>[Unit => A, A]         = Iso.unsafe(_(()), a => _ => a)
  def isoAToUnit[A]:     <=>[A => Unit, Unit]      = Iso.unsafe(_ => (), _ => _ => ())
  def isoVoidUnitU[A]:   <=>[Unit, Void => A]      = Iso.unsafe(_ => a => a, _ => ())
  def isoVoidUnit[A, B]: <=>[A => Unit, Void => B] = Iso.unsafe(_ => v => v, _ => _ => ())

  def isoTerminalInitial[->[_,_], T, I, A, TC[_]](implicit
    T: HasTerminalObject.Aux[->, TC, T],
    I: HasInitialObject.Aux[->, TC, I],
    TC: TC[A]
  ): (A -> T) <=> (I -> A) = Iso.unsafe(_ => I.initiate, _ => T.terminate)

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
}

final class IsoSyntaxOps[A](val self: A) extends AnyVal {
  def isoTo[B](implicit h: Iso.HasIso[* => *, A, B]): B = h(self)
}

import io.cosmo.exo.IsoHelperTraits._

trait IsoInstances extends IsoInstances1 {
  implicit def isoBifunctor[->[_,_], T[_], ⊙[_,_]](implicit
    sub: Subcat.Aux[->, T], B: Endobifunctor.Aux[->, T, ⊙],
  ): Endobifunctor.Aux[Iso[->, *, *], T, ⊙] =
    new IsoBifunctor[->, T, ⊙] {val cat = sub; val bif = B}

  implicit def isoGroupoid[->[_,_], T[_]](implicit C: Subcat.Aux[->, T]): Groupoid.Aux[Iso[->, *, *], T] =
    new IsoGroupoid[->, T] {val cat = C}

  implicit def isoAssoc[->[_,_], P[_,_], T[_]](implicit
    c: Subcat.Aux[->, T],
    a: Associative.Aux[->, P, T],
    b: Endobifunctor.Aux[->, T, P],
  ): Associative[Iso[->, *, *], P] = new IsoAssoc[->, T, P] {val cat = c; val A = a; val bif = b}
}

trait IsoInstances1 extends IsoInstances2 {
  implicit def isoBraided[->[_,_], P[_,_], T[_]](implicit
    c: Subcat.Aux[->, T],
    a: Braided.Aux[->, P, T],
    b: Endobifunctor.Aux[->, T, P],
  ): Braided.Aux[Iso[->, *, *], P, T] =
    new IsoBraided[->, P, T] {val cat = c; val A = a; val bif = b}

  implicit def isoMonoidal[->[_,_], P[_,_], T[_], I](implicit
    c: Subcat.Aux[->, T],
    a: Monoidal.Aux[->, P, T, I],
    b: Endobifunctor.Aux[->, T, P],
  ): Monoidal.Aux[Iso[->, *, *], P, T, I] =
    new IsoMonoidal[->, P, T, I] {val cat = c; val A = a; val bif = b}
}
trait IsoInstances2 {
  implicit def isoSymmetric[->[_,_], P[_,_], T[_]](implicit
    c: Subcat.Aux[->, T],
    a: Symmetric.Aux[->, P, T],
    b: Endobifunctor.Aux[->, T, P],
  ): Symmetric.Aux[Iso[->, *, *], P, T] =
    new IsoSymmetric[->, P, T] {val cat = c; val A = a; val bif = b}
}

object IsoHelperTraits {

  trait IsoBifunctor[->[_,_], T[_], P[_,_]] extends Endobifunctor[Iso[->, *, *], P] {
    def cat: Subcat.Aux[->, T]
    def bif: Endobifunctor.Aux[->, T, P]
    type TCL[a] = T[a]
    type TCR[a] = T[a]
    type TC[a] = T[a]
    val L, R, C = Iso.isoGroupoid[->, T](cat)
    override def bimap[A, X, B, Y](l: Iso[->, A, X], r: Iso[->, B, Y]): Iso[->, P[A, B], P[X, Y]] = {
      Iso.unsafe(bif.bimap(l.to, r.to), bif.bimap(l.from, r.from))(cat)
    }
  }

  trait IsoGroupoid[->[_,_], T[_]] extends Groupoid[Iso[->, *, *]] {
    def cat: Subcat.Aux[->, T]
    type TC[a] = T[a]
    def flip[A, B](f: Iso[->, A, B]) = f.flip
    def id[A](implicit A: T[A]) = Iso.refl[->, A, TC](cat, A)
    def andThen[A, B, C](ab: Iso[->, A, B], bc: Iso[->, B, C]) = ab.andThen(bc)
  }

  trait IsoAssoc[->[_,_], T[_], ⊙[_,_]] extends Associative[Iso[->, *, *], ⊙] {
    def cat: Subcat.Aux[->, T]
    def A: Associative.Aux[->, ⊙, T]
    def bif: Endobifunctor.Aux[->, TC, ⊙]
    type TC[a] = T[a]
    def C = Iso.isoGroupoid[->, T](cat)
    def bifunctor = Iso.isoBifunctor(cat, bif)
    def associate[X, Y, Z] = Iso.unsafe(A.associate[X, Y, Z], A.diassociate[X, Y, Z])(cat)
    def diassociate[X, Y, Z] = Iso.unsafe(A.diassociate[X, Y, Z], A.associate[X, Y, Z])(cat)
  }

  trait IsoBraided[->[_,_], ⊙[_,_], T[_]] extends Braided[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    def A: Braided.Aux[->, ⊙, T]
    def braid[A, B] = Iso.unsafe(A.braid[A, B], A.braid[B, A])(cat)
  }

  trait IsoSymmetric[->[_,_], ⊙[_,_], T[_]] extends Symmetric[Iso[->, *, *], ⊙] with IsoBraided[->, ⊙, T] {
    def A: Symmetric.Aux[->, ⊙, T]
  }

  trait IsoMonoidal[->[_,_], ⊙[_,_], T[_], I] extends Monoidal[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    def A: Monoidal.Aux[->, ⊙, T, I]
    type Id = I
    def idl[A]: Iso[->, ⊙[Id, A], A] = Iso.unsafe(A.idl[A], A.coidl[A])(cat)
    def coidl[A] = Iso.unsafe(A.coidl[A], A.idl[A])(cat)
    def idr[A] = Iso.unsafe(A.idr[A], A.coidr[A])(cat)
    def coidr[A] = Iso.unsafe(A.coidr[A], A.idr[A])(cat)
  }

}
