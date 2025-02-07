package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.syntax.*

import scala.util.NotGiven

trait Iso[->[_,_], A, B]:
  self =>

  def cat: Semicategory[->]

  def to:   A -> B
  def from: B -> A

  final def apply(a: A)(using ev: =~~=[->, * => *]): B = ev(to)(a)

  private type <->[a, b] = Iso[->, a, b]

  lazy val flip: B <-> A = new Iso[->, B, A]:
    val (cat, to, from) = (self.cat, self.from, self.to)
    override lazy val flip = self

  private[this] given Semicategory[->] = cat

  final def andThen[C](that: B <-> C): A <-> C =
    Iso.unsafe(self.to >>> that.to, that.from >>> self.from)

  final def compose[Z](that: Z <-> A): Z <-> B = that.andThen(self)

  /** If A <-> B then having an arrow B -> B we can obtain A -> A */
  def teleport(f: A -> A): B -> B = self.from >>> f >>> self.to

  /** Having A <-> B searches implicits for B <-> C to obtain A <-> C */
  def chain[C](using i: HasIso[->, B, C]): A <-> C = self andThen i

  /** For some F[_] that has an iso functor, if we have an F[A] we can obtain an F[B] using A <-> B */
  def derive[F[_]](using fa: F[A], I: Exo.IsoFun[->, F]): F[B] = I.map(self)(fa)

  /** From A <-> B, X <-> Y we can obtain (A ⨂ X) <-> (B ⨂ Y) if -> has an Associative instance with ⨂ */
  def grouped[⨂[_,_]] = new GroupedPartial[⨂]
  class GroupedPartial[⨂[_,_]]:
    def apply[I, J](ij: I <-> J)(using A: Associative[->, ⨂]): ⨂[A, I] <-> ⨂[B, J] =
      Associative[<->, ⨂].bifunctor.bimap(self, ij)

  /** From A <-> B, X <-> Y we can obtain (A, X) <-> (B, Y) if -> has an Associative instance with Tuple2 */
  def and[I, J](ij: I <-> J)(using C: Associative[->, Tuple2]): (A, I) <-> (B, J) = grouped[Tuple2](ij)
  /** From A <-> B, X <-> Y we can obtain (A, X) <-> (B, Y) if -> has an Associative instance with Tuple2 */
  def /\ [I, J](ij: I <-> J)(using C: Associative[->, /\]): (A /\ I) <-> (B /\ J) = grouped[/\](ij)

  /** From A <-> B, X <-> Y we can obtain (A \/ X) <-> (B \/ Y) if -> has an associative instance with \/ */
  def or[I, J](ij: I <-> J)(using C: Associative[->, Either]): Either[A, I] <-> Either[B, J] = grouped[Either](ij)
  /** From A <-> B, X <-> Y we can obtain (A \/ X) <-> (B \/ Y) if -> has an associative instance with \/ */
  def \/[I, J](ij: I <-> J)(using C: Associative[->, \/]): (A \/ I) <-> (B \/ J) = grouped[\/](ij)

object Iso extends IsoInstances with IsoImplicits:
  def apply[->[_,_], A, B](using iso: HasIso[->, A, B]): Iso[->, A, B] = iso
  def apply[->[_,_], A](using SubcatHasId[->, A]): Iso[->, A, A] = refl[->, A]
  def apply[A]: A <=> A = refl[A]

  /** create an isomorphism given the two complementary functions as long as you promise they uphold the iso laws */
  def unsafe[->[_,_], A, B](ab: A -> B, ba: B -> A)(using C: Semicategory[->]): Iso[->, A, B] =
    new Iso[->, A, B] { val (cat, to, from) = (C, ab, ba) }

  def refl[->[_,_], A](using c: SubcatHasId[->, A]): Iso[->, A, A] =
    new Iso[->, A, A] { val cat = c.s; val to, from = c.id }

  private[this] val forall = ∀.of[[a] =>> a <=> a](<=>.unsafe(identity, identity))

  def refl[A]: A <=> A = forall[A]

  extension[->[_,_], F[_], G[_]](i: IsoK[->, F, G])
    def flipK: IsoK[->, G, F] = ∀.mk[IsoK[->, G, F]](i.apply.flip)
    def toK:   ∀[[a] =>> F[a] -> G[a]] = ∀[[a] =>> F[a] -> G[a]](i.apply.to)
    def fromK: ∀[[a] =>> G[a] -> F[a]] = ∀[[a] =>> G[a] -> F[a]](i.apply.from)
    def chainK[H[_]](using j: HasIsoK[->, G, H]): IsoK[->, F, H] = ∀.mk[IsoK[->, F, H]](i.apply andThen j.apply)
    def teleportK(f: ∀[[a] =>> F[a] -> F[a]]): ∀[[a] =>> G[a] -> G[a]] =
      ∀[[a] =>> G[a] -> G[a]](i.apply.teleport(f.apply))
  extension[->[_,_], F[_,_], G[_,_]](i: IsoK2[->, F, G])
    def flipK2: IsoK2[->, G, F] = ∀∀.mk[IsoK2[->, G, F]](i.apply.flip)
    def toK2:   ∀∀[[a, b] =>> F[a, b] -> G[a, b]] = ∀∀[[a, b] =>> F[a, b] -> G[a, b]](i.apply.to)
    def fromK2: ∀∀[[a, b] =>> G[a, b] -> F[a, b]] = ∀∀[[a, b] =>> G[a, b] -> F[a, b]](i.apply.from)
    def chainK2[H[_,_]](using j: HasIsoK2[->, G, H]): IsoK2[->, F, H] = ∀∀.mk[IsoK2[->, F, H]](i.apply andThen j.apply)
    def teleportK2(f: ∀∀[[a, b] =>> F[a, b] -> F[a, b]]): ∀∀[[a, b] =>> G[a, b] -> G[a, b]] =
      ∀∀[[a, b] =>> G[a, b] -> G[a, b]](i.apply.teleport(f.apply))
  extension[->[_,_], A[_[_]], B[_[_]]](i: IsoH[->, A, B])
    def flipH: IsoH[->, B, A] = ∀~.mk[IsoH[->, B, A]](i.apply.flip)
    def toH:   ∀~[[f[_]] =>> A[f] -> B[f]] = ∀~[[f[_]] =>> A[f] -> B[f]](i.apply.to)
    def fromH: ∀~[[f[_]] =>> B[f] -> A[f]] = ∀~[[f[_]] =>> B[f] -> A[f]](i.apply.from)
    def chainH[C[_[_]]](using j: HasIsoH[->, B, C]): IsoH[->, A, C] = ∀~.mk[IsoH[->, A, C]](i.apply andThen j.apply)
    def teleportH(f: ∀~[[f[_]] =>> A[f] -> A[f]]): ∀~[[f[_]] =>> B[f] -> B[f]] =
      ∀~[[f[_]] =>> B[f] -> B[f]](i.apply.teleport(f.apply))

  /** if I can transform an arrow into another then I can also transform the corresponding isomorphisms */
  def liftFnFnToFnIso[==>[_,_], -->[_,_] :Subcat](fn: ==> ~~> -->): Iso[==>, *, *] ~~> Iso[-->, *, *] =
    ~~>([A, B] => (i: Iso[==>, A, B]) => Iso.unsafe[-->, A, B](fn.run(i.to), fn.run(i.from)))

  /** If two arrow are isomorphic then those arrows isomorphisms are isomorphic */
  def liftIsoFnToIso[==>[_,_] : Subcat, -->[_,_] : Subcat](iso: ==> <~~> -->): Iso[==>, *, *] <~~> Iso[-->, *, *] =
    IsoK2.unsafe(liftFnFnToFnIso[==>, -->](iso.toK2), liftFnFnToFnIso[-->, ==>](iso.fromK2))

  /** Isomorphism between any isomorphism and it's flipped self */
  given flippedIso[->[_,_], A, B](using n: A =!= B): (Iso[->, A, B] <=> Iso[->, B, A]) = Iso.unsafe(_.flip, _.flip)

end Iso

import IsoHelperTraits.*

trait IsoInstances extends IsoInstances01:
  given bifunctor[->[_,_], ⊙[_,_]](using S: Subcat[->], B: Endobifunctor[->, ⊙]): Endobifunctor[Iso[->, *, *], ⊙] =
    new IsoBifunctor[->, S.TC, ⊙] {val cat = S; val bif = B}
  given groupoid[->[_,_], T[_]](using C: Subcat.Aux[->, T]
  ): Groupoid.Aux[Iso[->, *, *], T] = new IsoGroupoid[->, T] {val cat = C}
  given associative[->[_,_], ⊙[_,_]](using
    a: Associative[->, ⊙]
  ): Associative.Aux[Iso[->, *, *], ⊙, a.TC] = new IsoAssoc[->, a.TC, ⊙] {val A = a}

trait IsoInstances01 extends IsoInstances02:
  given braided[->[_,_], ⊙[_,_]](using
    a: Braided[->, ⊙]
  ): Braided.Aux[Iso[->, *, *], ⊙, a.TC] = new IsoBraided[->, ⊙, a.TC] {val A = a}
  given monoidal[->[_,_], ⊙[_,_]](using
    a: Monoidal[->, ⊙]
  ): Monoidal.Aux[Iso[->, *, *], ⊙, a.TC, a.Id] = new IsoMonoidal[->, ⊙, a.TC, a.Id] {val A = a}

trait IsoInstances02:
  given symmetric[->[_,_], ⊙[_,_]](using
    a: Symmetric[->, ⊙]
  ): Symmetric.Aux[Iso[->, *, *], ⊙, a.TC] = new IsoSymmetric[->, ⊙, a.TC] {val A = a}

private[exo] object IsoHelperTraits:
  trait IsoBifunctor[->[_,_], ->#[_], ⊙[_,_]] extends Endobifunctor[Iso[->,*,*], ⊙]:
    given cat: Subcat.Aux[->, ->#]
    def bif: Endobifunctor[->, ⊙]
    private type <->[a,b] = Iso[->, a, b]
    override def bimap[A, X, B, Y](l: A <-> X, r: B <-> Y): ⊙[A, B] <-> ⊙[X, Y] =
      Iso.unsafe(bif.bimap(l.to, r.to), bif.bimap(l.from, r.from))

  trait IsoGroupoid[->[_,_], T[_]] extends Groupoid[Iso[->, *, *]]:
    given cat: Subcat.Aux[->, T]
    type TC[a] = T[a]
    def id[A](using A: T[A]): Iso[->, A, A] = Iso.refl[->, A](using SubcatHasId.from)
    def flip[A, B](f: Iso[->, A, B]): Iso[->, B, A] = f.flip
    def andThen[A, B, C](ab: Iso[->, A, B], bc: Iso[->, B, C]): Iso[->, A, C] = ab.andThen(bc)

  trait IsoAssoc[->[_,_], T[_], ⊙[_,_]] extends Associative[Iso[->, *, *], ⊙]:
    def A: Associative.Aux[->, ⊙, T]
    type TC[a] = T[a]
    def C = Iso.groupoid(using A.C)
    def bifunctor = Iso.bifunctor(using A.C, A.bifunctor)
    def associate  [X: TC, Y: TC, Z: TC]: Iso[->, X ⊙ Y ⊙ Z, X ⊙ (Y ⊙ Z)] = Iso.unsafe(A.associate[X, Y, Z], A.diassociate[X, Y, Z])(using A.C)
    def diassociate[X: TC, Y: TC, Z: TC]: Iso[->, X ⊙ (Y ⊙ Z), X ⊙ Y ⊙ Z] = Iso.unsafe(A.diassociate[X, Y, Z], A.associate[X, Y, Z])(using A.C)

  trait IsoBraided[->[_,_], ⊙[_,_], T[_]] extends Braided[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙]:
    def A: Braided.Aux[->, ⊙, T]
    def braid[A: TC, B: TC]: Iso[->, A ⊙ B, B ⊙ A] = Iso.unsafe(A.braid[A, B], A.braid[B, A])(using A.C)

  trait IsoSymmetric[->[_,_], ⊙[_,_], T[_]] extends Symmetric[Iso[->, *, *], ⊙] with IsoBraided[->, ⊙, T]:
    def A: Symmetric.Aux[->, ⊙, T]

  trait IsoMonoidal[->[_,_], ⊙[_,_], T[_], I] extends Monoidal[Iso[->, *, *], ⊙] with IsoAssoc[->, T, ⊙]:
    def A: Monoidal.Aux[->, ⊙, T, I]
    type Id = I
    def idl  [A: TC]: Iso[->, I ⊙ A, A] = Iso.unsafe(A.idl[A], A.coidl[A])(using A.C)
    def coidl[A: TC]: Iso[->, A, I ⊙ A] = Iso.unsafe(A.coidl[A], A.idl[A])(using A.C)
    def idr  [A: TC]: Iso[->, A ⊙ I, A] = Iso.unsafe(A.idr[A], A.coidr[A])(using A.C)
    def coidr[A: TC]: Iso[->, A, A ⊙ I] = Iso.unsafe(A.coidr[A], A.idr[A])(using A.C)

trait IsoImplicits extends IsoImplicits01:

  /** Any singleton is isomorphic with unit */
  given isoUnitSingleton[A <: Singleton](using a: ValueOf[A]): (A <=> Unit) = Iso.unsafe(_ => (), _ => a.value)

  /** Any two singletons are isomorphic */
  given isoBetweenSingletons[A <: Singleton, B <: Singleton](using
    a: ValueOf[A], b: ValueOf[B], neq: NotGiven[A === B]
  ): (A <=> B) = Iso.unsafe(_ => b.value, _ => a.value)

  /** Isomorphisms from categorical constructs */
  given isoSymmetric[->[_,_], ⊙[_,_], A, B, T[_]](using
    S: Symmetric.Aux[->, ⊙, T], a: T[A], b: T[B], n: A =!= B
  ): Iso[->, A ⊙ B, B ⊙ A] = S.isoSymmetric(a, b)
  given isoUnitorL[->[_,_], ⊙[_,_], A, T[_], I](using
    M: Monoidal.Aux[->, ⊙, T, I], a: T[A]
  ): Iso[->, I ⊙ A, A] = M.isoUnitorL(a)
  given isoUnitorR[->[_,_], ⊙[_,_], A, T[_], I](using
    M: Monoidal.Aux[->, ⊙, T, I], a: T[A]
  ): Iso[->, A ⊙ I, A] = M.isoUnitorR(a)
  given isoCartesian[->[_,_], ⊙[_,_], A, B, C, T[_]](using
    C: Cartesian[->, ⊙] {type TC[a] = T[a]}, a: T[A], b: T[B], c: T[C]
  ): ((A -> B, A -> C) <=> (A -> ⊙[B, C])) = C.isoCartesian(using a, b, c)
  given isoCocartesian[->[_,_], ⊙[_,_], A, B, C, T[_]](using
    C: Cocartesian[->, ⊙] {type TC[a] = T[a]}, a: T[A], b: T[B], c: T[C]
  ): ((A -> C, B -> C) <=> ((A ⊙ B) -> C)) = C.isoCocartesian(using a, b, c)
  given isoDistributive[->[_,_], ⨂[_,_], ⨁[_,_], A, B, C, T[_]](using
    D: Distributive.Aux1[->, T, ⨂, ⨁], a: T[A], b: T[B], c: T[C]
  )(using T: T[(A ⨂ B) ⨁ (A ⨂ C)]): Iso[->, ⨂[A, ⨁[B, C]], ⨁[⨂[A, B], ⨂[A, C]]] = D.isoDistributive(using a, b, c)
  given isoInitialUnit[->[_,_], I, A, TC[_]](using
    I: Initial.Aux[->, TC, I], a: TC[A],
  ): ((I -> A) <=> Unit) = Iso.unsafe(_ => (), _ => I.initiate)
  given isoTerminalUnit[->[_,_], T, A, TC[_]](using
    T: Terminal.Aux[->, TC, T], a: TC[A],
  ): ((A -> T) <=> Unit) = Iso.unsafe(_ => (), _ => T.terminate)
  given isoTerminalInitial[->[_,_], T, I, A, B, TC[_]](using
    T: Terminal.Aux[->, TC, T], I: Initial.Aux[->, TC, I], a: TC[A], b: TC[B]
  ): ((A -> T) <=> (I -> B)) = Iso.unsafe(_ => I.initiate, _ => T.terminate)
  given isoCccAdjunction[->[_,_], ⊙[_,_], |->[_,_], A, B, C, TC[_]](using
    c: Ccc.Aux1[->, TC, ⊙, |->]
  ): ((A ⊙ B) -> C <=> (A -> (B |-> C))) = c.isoClosedAdjunction[A, B, C]
  given isoGroupoid[->[_,_], A, B](using
    G: Groupoid[->]
  ): ((A -> B) <=> Iso[->, A, B]) = Iso.unsafe(eq => Iso.unsafe(eq, G.flip(eq)), ieq => ieq.to)

  /** Isomorphisms from yoneda lemma and corollaries */
  given yoLemma[->[_,_], A, F[_]](using
    C: SubcatHasId[->, A], E: Exo.Cov[->, F]
  ): ((->[A, *] ~> F) <=> F[A]) = yoneda.lemmaYoIso
  given coyoLemma[->[_,_], A, F[_]](using
    C: SubcatHasId[->, A], E: Exo.Con[->, F]
  ): ((->[*, A] ~> F) <=> F[A]) = yoneda.lemmaCoyoIso
  given yoEmbedding[->[_,_], A, B](using
    C: SubcatHasId[->, A]
  ): (((->[A, *]) ~> ->[B, *]) <=> (B -> A)) = yoneda.yoEmbedding[->, A, B]
  given coyoEmbedding[->[_,_], A, B](using
    C: SubcatHasId[->, A]
  ): ((->[*, A] ~> ->[*, B]) <=> (A -> B)) = yoneda.coyoEmbedding[->, A, B]
  given yoDoubleEmbed[->[_,_], A, B](using
    cat: Subcat[->]
  ): ((A -> B) <=> ∀~[[f[_]] =>> Endofunctor[->, f] => f[A] -> f[B]]) = yoneda.yoDoubleEmbed
  given yoCorol[->[_,_], A, B](using
    CA: SubcatHasId[->, A], CB: SubcatHasId[->, B]
  ): ((->[A, *] <~> ->[B, *]) <=> Iso[->, B, A]) = yoneda.yoCorollary
  given coyoCorol[->[_,_], A, B](using
    CA: SubcatHasId[->, A], CB: SubcatHasId[->, B]
  ): ((->[*, A] <~> ->[*,  B]) <=> Iso[->, A, B]) = yoneda.coyoCorollary

  given isoUnitToA[A]: ((Unit => A) <=> A) = Iso.unsafe(_(()), a => _ => a)

trait IsoImplicits01 extends IsoImplicits02:
  /** Isomorphisms from categorical constructs (continuation) */
  given isoAssociator[->[_,_], ⊙[_,_], A, B, C, T[_]](using
    A: Associative.Aux[->, ⊙, T], a: T[A], b: T[B], c: T[C]
  ): Iso[->, (A ⊙ B) ⊙ C, A ⊙ (B ⊙ C)] = A.isoAssociator(a, b, c)
  given isoGroupoidFlip[->[_,_], A, B](using
    G: Groupoid[->], n: A =!= B
  ): ((A -> B) <=> (B -> A)) = Iso.unsafe(Groupoid[->].flip, Groupoid[->].flip)

trait IsoImplicits02:
  /** Isomorphism between two equal values */
  given fromIs[A, B](using eq: A === B): (A <=> B) = eq.toIso
