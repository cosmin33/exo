package io.cosmo.exo

import cats.Invariant
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.data.ProdCat.Dicat
import io.cosmo.exo.categories.functors.{Endobifunctor, Exofunctor}
import io.cosmo.exo._
import io.cosmo.exo.evidence.{=!=, =~~=, IsK2}
import io.cosmo.exo.internalstuff.TupleGeneric
import io.cosmo.exo.typeclasses.{HasTc, IsTypeF, TypeF}
import shapeless.tag.@@
import shapeless.{tag, the}

trait Iso[->[_,_], A, B] { ab =>
  type TC[_]
  def cat: Subcat.Aux[->, TC]
  def to:   A -> B
  def from: B -> A

  final def apply(a: A)(implicit ev: IsK2[->, * => *]): B = ev(to)(a)
  final def andThen[C](bc: Iso[->, B, C]): Iso.Aux[->, TC, A, C] =
    Iso.unsafe(cat.andThen(ab.to, bc.to), cat.andThen(bc.from, ab.from))(cat)

  def flip: Iso.Aux[->, TC, B, A] = new Iso[->, B, A] {
    type TC[a] = ab.TC[a]
    val cat = ab.cat
    val (to, from) = (ab.from, ab.to)
    override val flip = ab
  }
}

object Iso extends IsoInstances {
  type Aux[->[_,_], C[_], A, B] = Iso[->, A, B] { type TC[x] = C[x] }
  type AuxT[->[_,_], A, B] = Iso.Aux[->, Trivial.T1, A, B]
  type AuxF[C[_], A, B] = Iso.Aux[* => *, C, A, B]
  type AuxTF[A, B] = Iso.Aux[* => *, Trivial.T1, A, B]

  def apply[->[_,_], A, B](implicit iso: Iso[->, A, B]): Iso[->, A, B] = iso

  private final class Refl[A]() extends Iso[* => *, A, A] {
    type TC[a] = Trivial.T1[a]
    val cat = Semicategory.function1
    val to = identity
    val from = identity
  }
  private val refl_ : ∀[Refl] = ∀.of[Refl](new Refl())

  def refl[A]: Iso.AuxTF[A, A] = refl_[A]

  def refl[->[_,_], A, Cons[_]](implicit c: Subcat.Aux[->, Cons], cons: Cons[A]): Iso.Aux[->, Cons, A, A] =
    new Iso[->, A, A] {type TC[a] = Cons[a]; val cat = c; val to, from = c.id[A]}

  def unsafe[->[_,_], A, B, T[_]](ab: A -> B, ba: B -> A)(implicit C: Subcat.Aux[->, T]): Iso.Aux[->, T, A, B] =
    new Iso[->, A, B] {type TC[a] = T[a]; val cat = C; val (to, from) = (ab, ba)}

  def unsafeT[A, B](to: A => B, from: B => A): Iso.Aux[* => *, Trivial.T1, A, B] = unsafe(to, from)

  /** Isomorphism between a case class and a tuple of the proper arity (using shapeless) */
  def forCaseClass[S <: Product](implicit ev: TupleGeneric[S]): Iso.AuxTF[S, ev.Repr] =
    Iso.unsafeT(s => ev.to(s), t => ev.from(t))

  implicit final class IsoOps[->[_,_], A, B](val self: Iso[->, A, B]) extends AnyVal {

    def chain[C](implicit i: HasIso[->, B, C]): Iso[->, A, C] = self.andThen(i)

    def chainK[C[_]](implicit
      ev: -> =~~= FunK,
      ta: IsTypeF[A],
      tb: IsTypeF[B],
      i: HasIso[->, B, TypeF[C]],
    ): Iso[->, A, TypeF[C]] = self.andThen(i)

    def derive[F[_]](implicit fa: F[A], I: Exofunctor.InvF[F], eq: -> =~~= Function1): F[B] =
      I.map(Dicat[* => *, A, B](eq(self.to), eq(self.from)))(fa)

    def deriveK[TC[_[_]]](implicit
      tc: HasTc[TC, A],
      ta: IsTypeF[A],
      tb: IsTypeF[B],
      I: Exofunctor.Aux[Dicat[FunK, *, *], * => *, HasTc[TC, *], IsTypeF, Trivial.T1],
      eq: -> =~~= FunK,
    ): HasTc[TC, B] = I.map(Dicat(eq(self.to), eq(self.from)))(tc)

    def and[I, J, ⨂[_,_]](that: Iso[->, I, J])(implicit C: Cartesian[->, ⨂]): Iso[->, ⨂[A, I], ⨂[B, J]] =
      Iso.unsafe(C.pair(self.to, that.to), C.pair(self.from, that.from))(self.cat)

    def or[I, J, ⨁[_,_]](that: Iso[->, I, J])(implicit C: Cocartesian[->, ⨁]): Iso[->, ⨁[A, I], ⨁[B, J]] =
      Iso.unsafe(C.pair(self.to, that.to), C.pair(self.from, that.from))(self.cat)

    def %~(f: ->[A, A])(implicit C: Semicategory[->]): ->[B, B] = C.andThen(self.from, C.andThen(f, self.to))
  }

  implicit def isoUnitSingleton[A <: Singleton](implicit
    a: ValueOf[A]
  ): Iso.AuxTF[Unit, A] =
    Iso.unsafeT((_: Unit) => a.value, (_: A) => ())

  implicit def isoBetweenSingletons[A <: Singleton, B <: Singleton](implicit
    a: ValueOf[A],
    b: ValueOf[B],
    neq: A =!= B
  ): Iso.AuxTF[A, B] =
    Iso.unsafeT((_: A) => b.value, (_: B) => a.value)

  def isoUnitToA[A]:     Iso.AuxTF[Unit => A, A]         = Iso.unsafeT(_(()), a => _ => a)
  def isoAToUnit[A]:     Iso.AuxTF[A => Unit, Unit]      = Iso.unsafeT(_ => (), _ => _ => ())
  def isoVoidUnitU[A]:   Iso.AuxTF[Unit, Void => A]      = Iso.unsafeT(_ => a => a, _ => ())
  def isoVoidUnit[A, B]: Iso.AuxTF[A => Unit, Void => B] = Iso.unsafeT(_ => v => v, _ => _ => ())

  def isoTerminalInitial[->[_,_], T, I, A, TC[_]](implicit
    T: HasTerminalObject.Aux[->, TC, T],
    I: HasInitialObject.Aux[->, TC, I],
    TC: TC[A]
  ): Iso.AuxTF[A -> T, I -> A] = Iso.unsafeT(_ => I.initiate, _ => T.terminate)

  case class SingleOf[T, U <: {type TC[_]}](widen: T {type TC[a] = U#TC[a]})
  object SingleOf {
    implicit def mkSingleOf[T <: {type TC[_]}](implicit t: T): SingleOf[T, t.type] = SingleOf(t)
  }

  type HasIso[->[_,_], A, B] = Iso[->, A, B] @@ HasIsoOps
  object HasIso {
    type Aux[->[_,_], T[_], A, B] = Iso.Aux[->, T, A, B] @@ HasIsoOps
    def from[->[_,_], A, B](i: Iso[->, A, B]): HasIso[->, A, B] = tag[HasIsoOps][Iso[->,A,B]](i)
    def fromT[->[_,_], T[_], A, B](i: Iso.Aux[->, T, A, B]): HasIso.Aux[->, T, A, B] = tag[HasIsoOps][Iso.Aux[->,T,A,B]](i)
  }
  trait HasIsoOps
  object HasIsoOps extends HasIsoOps01 {
    implicit def hasIsoImpRefl[->[_,_], A, T[_]](implicit s: Subcat.Aux[->, T], t: T[A]): HasIso.Aux[->, T, A, A] =
      HasIso.fromT(Iso.refl[->, A, T])
  }
  trait HasIsoOps01 extends HasIsoOps02 {
    implicit def hasIsoImpAB[->[_,_], A, B, T[_]](implicit
      i: Iso.Aux[->, T, A, B]): HasIso.Aux[->, T, A, B] = HasIso.fromT(i)
  }
  trait HasIsoOps02 {
    implicit def hasIsoImpBA[->[_,_], A, B, T[_]](implicit
      i: Iso.Aux[->, T, B, A]): HasIso.Aux[->, T, A, B] = HasIso.fromT(i.flip)
  }

  // TODO: Sterg asta dupa ce testez instantele
  object Product {
    private[exo] type ⨂[A, B] = (A, B)
    private[exo] type Id = Unit
    final def associate[A, B, C]: <=>[A ⨂ (B ⨂ C), (A ⨂ B) ⨂ C] =
      unsafeT({ case (a, (b, c)) => ((a, b), c) }, { case ((a, b), c) => (a, (b, c)) })
    final def commute[A, B]: <=>[A ⨂ B, B ⨂ A] =
      unsafeT({ case (a, b) => (b, a) }, { case (b, a) => (a, b) })
    final def unitL[A]: <=>[A, Id ⨂ A] = unsafeT(a => ((), a), { case ((), a) => a })
    final def unitR[A]: <=>[A, A ⨂ Id] = unsafeT(a => (a, ()), { case (a, ()) => a })
    final def first [A, B, C](iso: A <=> C): <=>[A ⨂ B, C ⨂ B] = iso.and(refl[B])
    final def second[A, B, C](iso: B <=> C): <=>[A ⨂ B, A ⨂ C] = refl[A].and(iso)
  }
  // TODO: Sterg asta dupa ce testez instantele
  object Coproduct {
    private[exo] type ⨂ [A, B] = Either[A, B]
    private[exo] type Id = Void
    final def associate[A, B, C]: <=>[A ⨂ (B ⨂ C), (A ⨂ B) ⨂ C] =
      unsafeT(
        _.fold(a => Left(Left(a)), _.fold(b => Left(Right(b)), c => Right(c))),
        _.fold(_.fold(a => Left(a), b => Right(Left(b))), c => Right(Right(c)))
      )
    final def commute[A, B]: <=>[A ⨂ B, B ⨂ A] = unsafeT((e: ⨂[A, B]) => e.swap, (e: ⨂[B, A]) => e.swap)
    final def unitL[A]: <=>[A, Id ⨂ A] = unsafeT(a => Right(a), _.fold(n => Void.absurd(n), a => a))
    final def unitR[A]: <=>[A, A ⨂ Id] = unsafeT(a => Left(a), _.fold(a => a, n => Void.absurd(n)))
    final def first[A, B, C](iso: A <=> C): <=>[A ⨂ B, C ⨂ B] = iso.or(refl[B])
    final def second[A, B, C](iso: B <=> C): <=>[A ⨂ B, A ⨂ C] = refl[A].or(iso)
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
trait IsoInstances2 extends IsoInstances3 {
  implicit def isoSymmetric[->[_,_], P[_,_], T[_]](implicit
    c: Subcat.Aux[->, T],
    a: Symmetric.Aux[->, P, T],
    b: Endobifunctor.Aux[->, T, P],
  ): Symmetric.Aux[Iso[->, *, *], P, T] =
    new IsoSymmetric[->, P, T] {val cat = c; val A = a; val bif = b}
}
trait IsoInstances3 {
}

object IsoHelperTraits {

  trait IsoBifunctor[->[_,_], T[_], P[_,_]] extends Endobifunctor[Iso[->, *, *], P] {
    protected def cat: Subcat.Aux[->, T]
    protected def bif: Endobifunctor.Aux[->, T, P]
    type TCL[a] = T[a]
    type TCR[a] = T[a]
    type TC[a] = T[a]
    val L, R, C = Iso.isoGroupoid[->, T](cat)
    override def bimap[A, X, B, Y](l: Iso[->, A, X], r: Iso[->, B, Y]): Iso[->, P[A, B], P[X, Y]] = {
      Iso.unsafe(bif.bimap(l.to, r.to), bif.bimap(l.from, r.from))(cat)
    }
  }

  trait IsoGroupoid[->[_,_], T[_]] extends Groupoid[Iso[->, *, *]] {
    protected def cat: Subcat.Aux[->, T]
    type TC[a] = T[a]
    def flip[A, B](f: Iso[->, A, B]) = f.flip
    def id[A](implicit A: T[A]) = Iso.refl[->, A, TC](cat, A)
    def andThen[A, B, C](ab: Iso[->, A, B], bc: Iso[->, B, C]) = ab.andThen(bc)
  }

  trait IsoAssoc[->[_,_], T[_], ⊙[_,_]] extends Associative[Iso[->, *, *], ⊙] {
    protected def cat: Subcat.Aux[->, T]
    protected def A: Associative.Aux[->, ⊙, T]
    protected def bif: Endobifunctor.Aux[->, TC, ⊙]
    type TC[a] = T[a]
    def C = Iso.isoGroupoid[->, T](cat)
    def bifunctor = Iso.isoBifunctor(cat, bif)
    def associate[X, Y, Z] = Iso.unsafe(A.associate[X, Y, Z], A.diassociate[X, Y, Z])(cat)
    def diassociate[X, Y, Z] = Iso.unsafe(A.diassociate[X, Y, Z], A.associate[X, Y, Z])(cat)
  }

  trait IsoBraided[->[_,_], ⊙[_,_], T[_]] extends Braided[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    protected def A: Braided.Aux[->, ⊙, T]
    def braid[A, B] = Iso.unsafe(A.braid[A, B], A.braid[B, A])(cat)
  }

  trait IsoSymmetric[->[_,_], ⊙[_,_], T[_]] extends Symmetric[Iso[->, *, *], ⊙] with IsoBraided[->, ⊙, T] {
    protected def A: Symmetric.Aux[->, ⊙, T]
  }

  trait IsoMonoidal[->[_,_], ⊙[_,_], T[_], I] extends Monoidal[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    protected def A: Monoidal.Aux[->, ⊙, T, I]
    type Id = I
    def idl[A]: Iso[->, ⊙[Id, A], A] = Iso.unsafe(A.idl[A], A.coidl[A])(cat)
    def coidl[A] = Iso.unsafe(A.coidl[A], A.idl[A])(cat)
    def idr[A] = Iso.unsafe(A.idr[A], A.coidr[A])(cat)
    def coidr[A] = Iso.unsafe(A.coidr[A], A.idr[A])(cat)
  }

}

object Balarie {

  val afd: Subcat.Aux[Function1, Trivial.T1] = Semicategory.function1

  implicitly[Subcat.Aux[Function1, Trivial.T1]]
  implicitly[Subcat[Function1]]

  val it: <=>[Int, Long] = Iso.unsafe((i: Int) => i.toLong, (l: Long) => l.toInt)

  implicit val li: List[Int] = List(1, 2)

  import cats.implicits._
  import io.cosmo.exo.categories.conversions.CatsInstances._

  val sdfs = the[Invariant[List]]

  val eeg: Exofunctor.InvF[List] = the[Exofunctor.InvF[List]]
  it.derive[List]

}

