package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

trait Iso[->[_,_], A, B] { self =>

  def cat: Subcat[->]

  def to: A -> B

  def from: B -> A

  final def apply(a: A)(implicit ev: =~~=[->, * => *]): B = ev(to)(a)

  private type <->[a, b] = Iso[->, a, b]

  lazy val flip: B <-> A = new Iso[->, B, A]:
    val (cat, to, from) = (self.cat, self.from, self.to)
    override lazy val flip = self

  private[this] given Subcat[->] = cat

  final def andThen[C](that: B <-> C): A <-> C =
    Iso.unsafe(self.to >>> that.to, that.from >>> self.from)

  final def compose[Z](that: Z <-> A): Z <-> B = that.andThen(self)

  /** If A <-> B then having a function B -> B we can obtain A -> A */
  def teleport(f: A -> A): B -> B = self.from >>> f >>> self.to

  /** Having A <-> B searches implicits for B <-> C to obtain A <-> C */
  def chain[C](using i: HasIso[->, B, C]): A <-> C = self andThen i

}

object Iso {
  def apply[->[_,_], A, B](using iso: HasIso[->, A, B]): Iso[->, A, B] = iso
  def apply[->[_,_], A](using SubcatHasId[->, A]): Iso[->, A, A] = refl[->, A]
  def apply[A]: A <=> A = refl[A]

  /** create an isomorphism given the two complementary functions as long as you promise they uphold the iso laws */
  def unsafe[->[_,_], A, B](ab: A -> B, ba: B -> A)(using C: Subcat[->]): Iso[->, A, B] =
    new Iso[->, A, B] { val (cat, to, from) = (C, ab, ba) }

  def refl[->[_,_], A](using c: SubcatHasId[->, A]): Iso[->, A, A] =
    new Iso[->, A, A] { val cat = c.s; val to, from = c.id }

  private[this] val forall = ∀.of[[a] =>> a <=> a].from(<=>.unsafe(identity, identity))

  def refl[A]: A <=> A = forall[A]

  /** if I can transform an arrow into another then I can also transform the corresponding isomorphisms */
  def liftFnFnToFnIso[==>[_,_], -->[_,_] :Subcat](fn: ==> ~~> -->): Iso[==>, *, *] ~~> Iso[-->, *, *] =
    ~~>([A, B] => (i: Iso[==>, A, B]) => Iso.unsafe[-->, A, B](fn.run(i.to), fn.run(i.from)))

  /** If two arrow are isomorphic then those arrows isomorphisms are isomorphic */
  def liftIsoFnToIso[==>[_,_] : Subcat, -->[_,_] : Subcat](iso: ==> <~~> -->): Iso[==>, *, *] <~~> Iso[-->, *, *] =
    <~~>.unsafe(liftFnFnToFnIso[==>, -->](iso.to), liftFnFnToFnIso[-->, ==>](iso.from))

  /** Isomorphism between any isomorphism and it's flipped self */
  given flippedIso[->[_,_], A, B]: (Iso[->, A, B] <=> Iso[->, B, A]) = Iso.unsafe(_.flip, _.flip)

}
