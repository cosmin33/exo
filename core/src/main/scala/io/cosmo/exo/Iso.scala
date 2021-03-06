package io.cosmo.exo

import io.cosmo.exo.Iso.HasIso
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.Exo
import io.cosmo.exo.categories.instances.isos.yoneda
import io.cosmo.exo.evidence.{=:!=, ===, =~=, =~~=, Is}
import io.cosmo.exo.internalstuff.TupleGeneric
import io.cosmo.exo.typeclasses.{HasTc, TypeK}
import io.estatico.newtype.macros.newtype
import shapeless.Generic

trait Iso[->[_,_], A, B] { ab =>
  // Laws: to >> from === from >>> to === cat.id
  def cat: Subcat[->]
  def to:   A -> B
  def from: B -> A

  private type <->[a, b] = Iso[->, a, b]

  final def apply(a: A)(implicit ev: =~~=[->, * => *]): B = ev(to)(a)

  final def andThen[C](bc: B <-> C): A <-> C =
    Iso.unsafe(cat.andThen(ab.to, bc.to), cat.andThen(bc.from, ab.from))(cat)

  final def compose[Z](za: Z <-> A): Z <-> B = za.andThen(ab)

  /** Flips the isomorphism from A <-> B to B <-> A grace to it's reflexivity property */
  lazy val flip: B <-> A = new (B <-> A) {
    val (cat, to, from) = (ab.cat, ab.from, ab.to)
    override lazy val flip = ab
  }

  /** If A <-> B then having a function B -> B we can obtain A -> A */
  def teleport(f: A -> A): B -> B = cat.andThen(ab.from, cat.andThen(f, ab.to))

  /** Having A <-> B searches implicits for B <-> C to obtain A <-> C */
  def chain[C](implicit i: HasIso[->, B, C]): A <-> C = ab.andThen(i)

  /** Having F <~> G searches implicits for G <~> H to obtain F <~> H */
  def chainK[C[_]](implicit i: HasIso[->, B, TypeK[C]]): A <-> TypeK[C] = ab.andThen(i)

  /** For some F[_] that has an iso functor, if we have an F[A] we can obtain an F[B] using A <-> B */
  def derive[F[_]](implicit fa: F[A], I: Exo.IsoFun[->, F]): F[B] = I.map(ab)(fa)

  /** Typeclass derivation: having TypeF[F] <-> TypeF[G] we can obtain HasTc[TC, A] => HasTc[TC, B] */
  def deriveK[TC[_[_]]](implicit
    tc: HasTc[TC, A],
    E: Exo.IsoFun[->, HasTc[TC, *]],
    k: IsKind[B]
  ): TC[k.Type] = E.map(ab)(tc).instanceFor(k)

  /** From A <-> B, X <-> Y we can obtain (A ⨂ X) <-> (B ⨂ Y) if -> has an Associative instance with ⨂ */
  def grouped[⨂[_,_]] = new GroupedPartial[⨂]
  class GroupedPartial[⨂[_,_]] {
    def apply[I, J](ij: I <-> J)(implicit A: Associative[->, ⨂]): ⨂[A, I] <-> ⨂[B, J] =
      Associative[Iso[->,*,*], ⨂].grouped(ab, ij)
  }

  /** From A <-> B, X <-> Y we can obtain (A, X) <-> (B, Y) if -> has an Associative instance with Tuple2 */
  def and [I, J](ij: I <-> J)(implicit C: Associative[->, Tuple2]): (A, I) <-> (B, J) = grouped[Tuple2](ij)
  def and_[I, J](ij: I <-> J)(implicit C: Associative[->, /\]): (A /\ I) <-> (B /\ J) = grouped[/\](ij)

  /** From A <-> B, X <-> Y we can obtain (A \/ X) <-> (B \/ Y) if -> has an associative instance with \/ */
  def or [I, J](ij: I <-> J)(implicit C: Associative[->, Either]): (A Either I) <-> (B Either J) = grouped[Either](ij)
  def or_[I, J](ij: I <-> J)(implicit C: Associative[->, \/]): (A \/ I) <-> (B \/ J) = grouped[\/](ij)

}

object Iso extends IsoInstances with IsoInstancesEq {
  def apply[->[_,_], A, B](implicit iso: HasIso[->, A, B]): Iso[->, A, B] = iso.iso
  def apply[->[_,_], A](implicit si: SubcatHasId[->, A]): Iso[->, A, A] = refl[->, A]
  def apply[A]: Iso[* => *, A, A] = refl[A]

  private val reflAny: Iso[* => *, Any, Any] =
    new Iso[* => *, Any, Any] { val cat = Subcat[* => *]; val to, from = identity[Any] }

  def refl[A]: Iso[* => *, A, A] = reflAny.asInstanceOf[Iso[* => *, A, A]]

  def refl[->[_,_], A](implicit c: SubcatHasId[->, A]): Iso[->, A, A] =
    new Iso[->, A, A] {val cat = c.s; val to, from = c.id}

  /** create an isomorphism given the two complementary functions as long as you promise they uphold the iso laws */
  def unsafe[->[_,_], A, B](ab: A -> B, ba: B -> A)(implicit C: Subcat[->]): Iso[->, A, B] =
    new Iso[->, A, B] { val (cat, to, from) = (C, ab, ba) }

  /** if I can transform an arrow into another then I can also transform the corresponding isomorphisms */
  def liftFnFnToFnIso[==>[_,_]: Subcat, -->[_,_]: Subcat](fn: ==> ~~> -->): Iso[==>,*,*] ~~> Iso[-->,*,*] =
    ∀∀.mk[Iso[==>,*,*] ~~> Iso[-->,*,*]].from(i => Iso.unsafe(fn.exec(i.to),   fn.exec(i.from)))

  /** If two arrow are isomorphic then those arrows isomorphisms are isomorphic */
  implicit def liftIsoFnToIso[==>[_,_]: Subcat, -->[_,_]: Subcat](iso: ==> <~~> -->): Iso[==>,*,*] <~~> Iso[-->,*,*] =
    <~~>.unsafe(liftFnFnToFnIso(iso.to), liftFnFnToFnIso(iso.from))

  /** Isomorphism between a case class and a tuple of the proper arity (using shapeless) */
  implicit def forCaseClass[S <: Product](implicit ev: TupleGeneric[S]): Iso[* => *, S, ev.Repr] =
    Iso.unsafe(s => ev.to(s), t => ev.from(t))

  /** Isomorphism between a case class and it's generic representation (from shapeless) */
  def forGeneric[A, Repr](implicit g: Generic.Aux[A, Repr]): A <=> Repr = Iso.unsafe(g.to, g.from)

  /** Isomorphism between any iso and it's flipped iso */
  implicit def flippedIso[->[_,_], A, B]: Iso[->, A, B] <=> Iso[->, B, A] = Iso.unsafe(_.flip, _.flip)

  /** Any singleton is isomorphic with unit */
  implicit def isoUnitSingleton[A <: Singleton](implicit
    a: ValueOf[A]
  ): A <=> Unit = Iso.unsafe((_: A) => (), (_: Unit) => a.value)

  /** Any two singletons are isomorphic */
  implicit def isoBetweenSingletons[A <: Singleton, B <: Singleton](implicit
    a: ValueOf[A], b: ValueOf[B], neq: A =:!= B
  ): A <=> B = Iso.unsafe((_: A) => b.value, (_: B) => a.value)

  /** Isomorphisms from categorical constructs */
  implicit def isoAssociator[->[_,_], ⊙[_,_], A, B, C, T[_]](implicit
    A: Associative.Aux[->, ⊙, T], a: T[A], b: T[B], c: T[C]
  ): Iso[->, (A ⊙ B) ⊙ C, A ⊙ (B ⊙ C)] = A.isoAssociator(a, b, c)
  implicit def isoSymmetric[->[_,_], ⊙[_,_], A, B, T[_]](implicit
    S: Symmetric.Aux[->, ⊙, T], a: T[A], b: T[B]
  ): Iso[->, A ⊙ B, B ⊙ A] = S.isoSymmetric(a, b)
  implicit def isoUnitorL[->[_,_], ⊙[_,_], A, T[_], I](implicit
    M: Monoidal.Aux[->, ⊙, T, I], a: T[A]
  ): Iso[->, I ⊙ A, A] = M.isoUnitorL(a)
  implicit def isoUnitorR[->[_,_], ⊙[_,_], A, T[_], I](implicit
    M: Monoidal.Aux[->, ⊙, T, I], a: T[A]
  ): Iso[->, A ⊙ I, A] = M.isoUnitorR(a)
  implicit def isoCartesian[->[_,_], ⊙[_,_], A, B, C, T[_]](implicit
    C: Cartesian[->, ⊙] {type TC[a] = T[a]}, b: T[B], c: T[C]
  ): (A -> B, A -> C) <=> (A -> ⊙[B, C]) = C.isoCartesian(b, c)
  implicit def isoCocartesian[->[_,_], ⊙[_,_], A, B, C, T[_]](implicit
    C: Cocartesian[->, ⊙] {type TC[a] = T[a]}, a: T[A], b: T[B]
  ): (A -> C, B -> C) <=> ((A ⊙ B) -> C) = C.isoCocartesian(a, b)
  implicit def isoDistributive[->[_,_], ⨂[_,_], ⨁[_,_], A, B, C, T[_]](implicit
    D: Distributive.Aux1[->, T, ⨂, ⨁], a: T[A], b: T[B], c: T[C]
  ): Iso[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]] = D.isoDistributive(a, b, c)
  implicit def isoTerminalUnit[->[_,_], T, A, TC[_]](implicit
    T: Terminal.Aux[->, TC, T], a: TC[A],
  ): (A -> T) <=> Unit = Iso.unsafe(_ => (), _ => T.terminate)
  implicit def isoInitialUnit[->[_,_], I, A, TC[_]](implicit
    I: Initial.Aux[->, TC, I], a: TC[A],
  ): (I -> A) <=> Unit = Iso.unsafe(_ => (), _ => I.initiate)
  implicit def isoTerminalInitial[->[_,_], T, I, A, B, TC[_]](implicit
    T: Terminal.Aux[->, TC, T], I: Initial.Aux[->, TC, I], a: TC[A], b: TC[B]
  ): (A -> T) <=> (I -> B) = Iso.unsafe(_ => I.initiate, _ => T.terminate)
  implicit def isoCccAdjunction[->[_,_], ⊙[_,_], |->[_,_], A, B, C, TC[_]](implicit
    c: Ccc.Aux1[->, TC, ⊙, |->]
  ): (A ⊙ B) -> C <=> (A -> (B |-> C)) = c.isoClosedAdjunction[A, B, C]
  implicit def isoGroupoid[->[_,_], A, B](implicit
    G: Groupoid[->]
  ): (A -> B) <=> Iso[->, A, B] = Iso.unsafe(eq => Iso.unsafe(eq, G.flip(eq)), ieq => ieq.to)
  implicit def isoGroupoidFlip[->[_,_], A, B](implicit
    G: Groupoid[->]
  ): (A -> B) <=> (B -> A) = Iso.unsafe(Groupoid[->].flip, Groupoid[->].flip)

  /** Isomorphisms from yoneda lemma and corollaries */
  implicit def isoYoLemma[->[_,_], ->#[_], A, F[_]](implicit
    C: SubcatHasId[->, A], E: Exo.Cov[->, F]
  ): ((A -> *) ~> F) <=> F[A] = yoneda.lemmaYoIso
  implicit def isoCoyoLemma[->[_,_], ->#[_], A, F[_]](implicit
    C: SubcatHasId[->, A], E: Exo.Con[->, F]
  ): ((* -> A) ~> F) <=> F[A] = yoneda.lemmaCoyoIso
  implicit def isoYoEmbeddingCov[->[_,_], ->#[_], A, B](implicit
    C: SubcatHasId[->, A]
  ): ((A -> *) ~> (B -> *)) <=> (B -> A) = yoneda.yoEmbeddingCov[->, A, B]
  implicit def isoYoEmbeddingCon[->[_,_], ->#[_], A, B](implicit
    C: SubcatHasId[->, A]
  ): ((* -> A) ~> (* -> B)) <=> (A -> B) = yoneda.yoEmbeddingCon[->, A, B]
  implicit def isoYoDoubleEmbed[->[_,_], A, B](implicit
    cat: Subcat[->]
  ): (A -> B) <=> ∀~[λ[f[_] => Endofunctor[->, f] => f[A] -> f[B]]] = yoneda.yoDoubleEmbed
  implicit def isoYoCorolCov[->[_,_], A, B](implicit
    CA: SubcatHasId[->, A], CB: SubcatHasId[->, B]
  ): ((A -> *) <~> (B -> *)) <=> Iso[->, B, A] = yoneda.yoCorol1Cov
  implicit def isoYoCorolCon[->[_,_], ->#[_], A, B](implicit
    CA: SubcatHasId[->, A], CB: SubcatHasId[->, B]
  ): ((* -> A) <~> (* -> B)) <=> Iso[->, A, B] = yoneda.yoCorol1Con

  implicit def isoUnitToA[A]: (Unit => A) <=> A = Iso.unsafe(_(()), a => _ => a)


  /** iso's for categorical constructs applied to tuple */
  object Product {
    final def associate[A, B, C]: (A, (B, C)) <=> ((A, B), C) =
      Iso.unsafe(p => ((p._1, p._2._1), p._2._2), { p => (p._1._1, (p._1._2, p._2)) })
    final def commute[A, B]: (A, B) <=> (B, A) = unsafe(_.swap, _.swap)
    final def unitL[A]: A <=> (Unit, A) = unsafe(a => ((), a), _._2)
    final def unitR[A]: A <=> (A, Unit) = unsafe(a => (a, ()), _._1)
    final def first [A, B, C](iso: A <=> C): (A, B) <=> (C, B) = iso.grouped(refl[B])
    final def second[A, B, C](iso: B <=> C): (A, B) <=> (A, C) = refl[A].grouped(iso)
  }

  /** iso's for categorical constructs applied to /\ */
  object Product1 {
    final def associate[A, B, C]: (A /\ (B /\ C)) <=> ((A /\ B) /\ C) =
      Iso.unsafe(p => /\(/\(p._1, p._2._1), p._2._2), p => /\(p._1._1, /\(p._1._2, p._2)))
    final def commute[A, B]: (A /\ B) <=> (B /\ A) = Iso.unsafe(_.swap, _.swap)
    final def unitL[A]: A <=> (Unit /\ A) = Iso.unsafe(a => /\((), a), _._2)
    final def unitR[A]: A <=> (A /\ Unit) = Iso.unsafe(a => /\(a, ()), _._1)
    final def first [A, B, C](iso: A <=> C): (A /\ B) <=> (C /\ B) = iso.grouped(refl[B])
    final def second[A, B, C](iso: B <=> C): (A /\ B) <=> (A /\ C) = refl[A].grouped(iso)
  }


  /** iso's for categorical constructs applied to Either */
  object Coproduct {
    final def associate[A, B, C]: (A Either (B Either C)) <=> ((A Either B) Either C) = Iso.unsafe(
      _.fold(a => Left(Left(a)), _.fold(b => Left(Right(b)), c => Right(c))),
      _.fold(_.fold(a => Left(a), b => Right(Left(b))), c => Right(Right(c))))
    final def commute[A, B]: (A Either B) <=> (B Either A) = Iso.unsafe(_.swap, _.swap)
    final def unitL[A]: A <=> Either[Void, A] = unsafe(a => Right(a), _.fold((n: A) => n, identity))
    final def unitR[A]: A <=> Either[A, Void] = unsafe(a => Left(a), _.fold(identity, (n: A) => n))
    final def first [A, B, C](iso: A <=> C): (A Either B) <=> (C Either B) = iso.grouped(refl[B])
    final def second[A, B, C](iso: B <=> C): (A Either B) <=> (A Either C) = refl[A].grouped(iso)
  }

  /** iso's for categorical constructs applied to \/ */
  object Coproduct1 {
    final def associate[A, B, C]: (A \/ (B \/ C)) <=> ((A \/ B) \/ C) = Iso.unsafe(
      _.fold(a => -\/(-\/(a)), _.fold(b => -\/(\/-(b)), c => \/-(c))),
      _.fold(_.fold(a => -\/(a), b => \/-(-\/(b))), c => \/-(\/-(c))))
    final def commute[A, B]: (A \/ B) <=> (B \/ A) = unsafe(_.swap, _.swap)
    final def unitL[A]: A <=> (Void \/ A) = unsafe(a => \/-(a), _.fold((n: A) => n, identity))
    final def unitR[A]: A <=> (A \/ Void) = unsafe(a => -\/(a), _.fold(identity, (n: A) => n))
    final def first [A, B, C](iso: A <=> C): (A \/ B) <=> (C \/ B) = iso.grouped(refl[B])
    final def second[A, B, C](iso: B <=> C): (A \/ B) <=> (A \/ C) = refl[A].grouped(iso)
  }

  /** Class equivalent to an Iso; useful for implicit searching of isomorphisms as it searches also for flipped iso and for reflective iso */
  @newtype case class HasIso[->[_,_], A, B](iso: Iso[->, A, B])
  object HasIso {
    implicit def impl[->[_,_], A, B](implicit
      e: EqImpIso[->, A, B] \/ Iso[->, A, B] \/ Iso[->, B, A]
    ): HasIso[->, A, B] =
      e.fold3(eqIso => HasIso(eqIso.iso), ab => HasIso(ab), ba => HasIso(ba.flip))

    implicit def conversionToIso[->[_, _], A, B](hi: HasIso[->, A, B]): Iso[->, A, B] = hi.iso
  }
  @newtype private[exo] case class ReflImpIso[->[_,_], A](iso: Iso[->, A, A])
  private[exo] object ReflImpIso {
    implicit def impl[->[_,_], A](implicit s: SubcatHasId[->, A]): ReflImpIso[->, A] =
      ReflImpIso(Iso.refl[->, A])
  }
  @newtype private[exo] case class EqImpIso[->[_,_], A, B](iso: Iso[->, A, B])
  private[exo] object EqImpIso {
    implicit def impl[->[_,_], A, B](implicit eq: A === B, r: ReflImpIso[->, A]): EqImpIso[->, A, B] =
      EqImpIso(eq.subst(r.iso))
  }

  /** Class equivalent to an IsoK; useful for implicit searching of isomorphisms as it searches also for flipped iso and for reflective iso */
  @newtype case class HasIsoK[->[_,_], F[_], G[_]](iso: IsoK[->, F, G])
  object HasIsoK {
    implicit def impl[->[_,_], F[_], G[_]](implicit
      e: EqImpIsoK[->, F, G] \/ IsoK[->, F, G] \/ IsoK[->, G, F]
    ): HasIsoK[->, F, G] =
      e.fold3(
        ei => HasIsoK(ei.iso),
        ab => HasIsoK(ab),
        ba => HasIsoK(∀.mk[IsoK[->, F, G]].from(ba.apply.flip))
      )

    implicit def conversionToIso[->[_, _], F[_], G[_]](hi: HasIsoK[->, F, G]): ∀[λ[a => Iso[->, F[a], G[a]]]] = hi.iso
  }
  @newtype private[exo] case class ReflImpIsoK[->[_,_], F[_]](iso: ∀[λ[a => Iso[->, F[a], F[a]]]])
  private[exo] object ReflImpIsoK {
    implicit def impl[->[_,_], F[_], T[_]](implicit s: Subcat.Aux[->, T], tc: ∀[λ[a => T[F[a]]]]): ReflImpIsoK[->, F] =
      ReflImpIsoK(∀.of[λ[a => Iso[->, F[a], F[a]]]].fromH(t => Iso.refl[->, F[t.T]](SubcatHasId.from(s, tc[t.T]))))
  }
  @newtype private[exo] case class EqImpIsoK[->[_,_], F[_], G[_]](iso: ∀[λ[a => Iso[->, F[a], G[a]]]])
  private[exo] object EqImpIsoK {
    implicit def impl[->[_,_], F[_], G[_]](implicit eq: F =~= G, r: ReflImpIsoK[->, F]): EqImpIsoK[->, F, G] =
      EqImpIsoK(eq.subst[λ[f[_] => ∀[λ[a => Iso[->, F[a], f[a]]]]]](r.iso))
  }

  object syntax extends IsoSyntax
}

trait IsoSyntax {
  implicit def toIsoOps[A](self: A): IsoSyntaxOps[A] = new IsoSyntaxOps(self)
  implicit def toIsokOps[F[_]](self: TypeK[F]): IsokSyntaxOps[F] = new IsokSyntaxOps(self)
}

final class IsokSyntaxOps[F[_]](val self: TypeK[F]) extends AnyVal {
  def isoWith[G[_]](implicit h: HasIso[FunK, TypeK[F], TypeK[G]]): F <~> G = FunK.isoKIso(h.iso)
}
final class IsoSyntaxOps[A](val self: A) extends AnyVal {
  def isoTo[B](implicit h: Iso.HasIso[* => *, A, B]): B = h(self)
}

/** Isomorphisms derived from lifting equalities */
trait IsoInstancesEq extends IsoInstancesEq1 {
  implicit def eqLift1[F[_], A, X](implicit eq: A === X): F[A] <=> F[X] = Is.lift(eq).toIso
  implicit def eqKLift1[A[_[_]], F[_], F1[_]](implicit eq: F =~= F1): A[F] <=> A[F1] = =~=.lower(eq).toIso
  implicit def eqK2Lift1[A[_[_,_]], F[_,_], F1[_,_]](implicit eq: F =~~= F1): A[F] <=> A[F1] = =~~=.lower(eq).toIso
}
trait IsoInstancesEq1 extends IsoInstancesEq2 {
  implicit def eqLift2[F[_,_], A, X, B, Y](implicit e1: A === X, e2: B === Y): F[A, B] <=> F[X, Y] = Is.lift2(e1, e2).toIso
  implicit def eqKLift2[A[_[_],_[_]], F[_], F1[_], G[_], G1[_]](implicit
    e1: F =~= F1, e2: G =~= G1
  ): A[F, G] <=> A[F1, G1] = =~=.lower2(e1, e2).toIso
  implicit def eqK2Lift2[A[_[_,_], _[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1
  ): A[F, G] <=> A[F1, G1] = =~~=.lower2.on(e1, e2).toIso
}
trait IsoInstancesEq2 extends IsoInstancesEq3 {
  implicit def eqLift3[F[_,_,_], A, X, B, Y, C, Z](implicit e1: A === X, e2: B === Y, e3: C === Z): F[A, B, C] <=> F[X, Y, Z] = Is.lift3(e1, e2, e3).toIso
  implicit def eqKLift3[A[_[_],_[_],_[_]], F[_], F1[_], G[_], G1[_], H[_], H1[_]](implicit
    e1: F =~= F1, e2: G =~= G1, e3: H =~= H1
  ): A[F, G, H] <=> A[F1, G1, H1] = =~=.lower3(e1, e2, e3).toIso
  implicit def eqK2Lift3[A[_[_,_],_[_,_],_[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1, e3: H =~~= H1
  ): A[F, G, H] <=> A[F1, G1, H1] = =~~=.lower3.on(e1, e2, e3).toIso
}
trait IsoInstancesEq3 extends IsoInstancesEq4{
  implicit def eqLift4[F[_,_,_,_], A, X, B, Y, C, Z, D, T](implicit e1: A === X, e2: B === Y, e3: C === Z, e4: D === T): F[A, B, C, D] <=> F[X, Y, Z, T] = Is.lift4(e1, e2, e3, e4).toIso
  implicit def eqKLift4[A[_[_],_[_],_[_],_[_]], F[_], F1[_], G[_], G1[_], H[_], H1[_], I[_], I1[_]](implicit
    e1: F =~= F1, e2: G =~= G1, e3: H =~= H1, e4: I =~= I1
  ): A[F, G, H, I] <=> A[F1, G1, H1, I1] = =~=.lower4(e1, e2, e3, e4).toIso
  implicit def eqK2Lift4[A[_[_,_],_[_,_],_[_,_],_[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_], I[_,_], I1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1, e3: H =~~= H1, e4: I =~~= I1
  ): A[F, G, H, I] <=> A[F1, G1, H1, I1] = =~~=.lower4.on(e1, e2, e3, e4).toIso
}
trait IsoInstancesEq4 {
  implicit def eqK2Lift5[A[_[_,_],_[_,_],_[_,_],_[_,_],_[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_], I[_,_], I1[_,_], J[_,_], J1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1, e3: H =~~= H1, e4: I =~~= I1, e5: J =~~= J1
  ): A[F, G, H, I, J] <=> A[F1, G1, H1, I1, J1] = =~~=.lower5.on(e1, e2, e3, e4, e5).toIso
}

import io.cosmo.exo.IsoHelperTraits._

trait IsoInstances extends IsoInstances1 {
  implicit def isoBifunctor[->[_,_], ->#[_], ⊙[_,_]](implicit
    S: Subcat.Aux[->, ->#], B: Endobifunctor[->, ⊙],
  ): Endobifunctor[Iso[->, *, *], ⊙] =
    new IsoBifunctor[->, ->#, ⊙] {val cat = S; val bif = B}

  implicit def isoGroupoid[->[_,_], T[_]](implicit C: Subcat.Aux[->, T]
  ): Groupoid.Aux[Iso[->, *, *], T] = new IsoGroupoid[->, T] {val cat = C}

  implicit def isoAssoc[->[_,_], ⊙[_,_]](implicit
    a: Associative[->, ⊙]
  ): Associative.Aux[Iso[->, *, *], ⊙, a.TC] = new IsoAssoc[->, a.TC, ⊙] {val A = a}
}
trait IsoInstances1 extends IsoInstances2 {
  implicit def isoBraided[->[_,_], ⊙[_,_]](implicit
    a: Braided[->, ⊙]
  ): Braided.Aux[Iso[->, *, *], ⊙, a.TC] = new IsoBraided[->, ⊙, a.TC] {val A = a}

  implicit def isoMonoidal[->[_,_], ⊙[_,_]](implicit
    a: Monoidal[->, ⊙]
  ): Monoidal.Aux[Iso[->, *, *], ⊙, a.TC, a.Id] = new IsoMonoidal[->, ⊙, a.TC, a.Id] {val A = a}
}
trait IsoInstances2 extends IsoInstances3 {
  implicit def isoSymmetric[->[_,_], ⊙[_,_]](implicit
    a: Symmetric[->, ⊙]
  ): Symmetric.Aux[Iso[->, *, *], ⊙, a.TC] = new IsoSymmetric[->, ⊙, a.TC] {val A = a}
}
trait IsoInstances3 {

}

private[exo] object IsoHelperTraits {

  trait IsoBifunctor[->[_,_], ->#[_], ⊙[_,_]] extends Endobifunctor[Iso[->,*,*], ⊙] {
    def cat: Subcat.Aux[->, ->#]
    def bif: Endobifunctor[->, ⊙]
    private type <->[a,b] = Iso[->, a, b]
    override def bimap[A, X, B, Y](l: A <-> X, r: B <-> Y): ⊙[A, B] <-> ⊙[X, Y] =
      Iso.unsafe(bif.bimap(l.to, r.to), bif.bimap(l.from, r.from))(cat)
  }

  trait IsoGroupoid[->[_,_], T[_]] extends Groupoid[Iso[->, *, *]] {
    def cat: Subcat.Aux[->, T]
    type TC[a] = T[a]
    def id[A](implicit A: T[A]): Iso[->, A, A] = Iso.refl[->, A](SubcatHasId.from(cat, A))
    def flip[A, B](f: Iso[->, A, B]): Iso[->, B, A] = f.flip
    def andThen[A, B, C](ab: Iso[->, A, B], bc: Iso[->, B, C]): Iso[->, A, C] = ab.andThen(bc)
  }

  trait IsoAssoc[->[_,_], T[_], ⊙[_,_]] extends Associative[Iso[->, *, *], ⊙] {
    def A: Associative.Aux[->, ⊙, T]
    type TC[a] = T[a]
    def C = Iso.isoGroupoid(A.C)
    def bifunctor = Iso.isoBifunctor(A.C, A.bifunctor)
    def associate  [X: TC, Y: TC, Z: TC]  : Iso[->, X ⊙ Y ⊙ Z, X ⊙ (Y ⊙ Z)] = Iso.unsafe(A.associate[X, Y, Z], A.diassociate[X, Y, Z])(A.C)
    def diassociate[X: TC, Y: TC, Z: TC]: Iso[->, X ⊙ (Y ⊙ Z), X ⊙ Y ⊙ Z] = Iso.unsafe(A.diassociate[X, Y, Z], A.associate[X, Y, Z])(A.C)
  }

  trait IsoBraided[->[_,_], ⊙[_,_], T[_]] extends Braided[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    def A: Braided.Aux[->, ⊙, T]
    def braid[A: TC, B: TC]: Iso[->, A ⊙ B, B ⊙ A] = Iso.unsafe(A.braid[A, B], A.braid[B, A])(A.C)
  }

  trait IsoSymmetric[->[_,_], ⊙[_,_], T[_]] extends Symmetric[Iso[->, *, *], ⊙] with IsoBraided[->, ⊙, T] {
    def A: Symmetric.Aux[->, ⊙, T]
  }

  trait IsoMonoidal[->[_,_], ⊙[_,_], T[_], I] extends Monoidal[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙] {
    def A: Monoidal.Aux[->, ⊙, T, I]
    type Id = I
    def idl  [A: TC]: Iso[->, I ⊙ A, A  ] = Iso.unsafe(A.idl[A], A.coidl[A])(A.C)
    def coidl[A: TC]: Iso[->,   A, I ⊙ A] = Iso.unsafe(A.coidl[A], A.idl[A])(A.C)
    def idr  [A: TC]: Iso[->, A ⊙ I, A  ] = Iso.unsafe(A.idr[A], A.coidr[A])(A.C)
    def coidr[A: TC]: Iso[->,   A, A ⊙ I] = Iso.unsafe(A.coidr[A], A.idr[A])(A.C)
  }

}
