package io.cosmo.exo

import io.cosmo.exo.evidence.*

val Forall2: Forall2Module = Forall2Impl
val ∀∀ : Forall2.type = Forall2
type Forall2[F[_,_]] = Forall2.Forall2[F]
type ∀∀[F[_,_]] = Forall2.Forall2[F]

private[exo] sealed trait Forall2Module {
  type Forall2[F[_,_]]
  type ∀∀[F[_,_]] = Forall2[F]

  trait Prototype[F[_,_]]:
    def apply[A, B]: F[A, B]
    final def make: ∀∀[F] = from(this)

  def specialize[F[_,_], A, B](f: ∀∀[F]): F[A, B]
  def instantiation[F[_,_], A, B]: ∀∀[F] <~< F[A, B]
  def monotonicity[F[_,_], G[_,_]](ev: ∀∀[[a, b] =>> F[a, b] <~< G[a, b]]): ∀∀[F] <~< ∀∀[G]
  def from[F[_,_]](p: Prototype[F]): ∀∀[F]
  def of[F[_,_]]: MkForall2[F]
  def mk[X](implicit u: Unapply[X]): MkForall2[u.F] = of[u.F]

  sealed trait MkForall2[F[_,_]] extends Any:
    type T
    type U
    def from(ft: F[T, U]): ∀∀[F]
    def apply(ft: F[T, U]): ∀∀[F] = from(ft)
    def fromH(ft: [T, U] => () => F[T, U]): Forall2[F] = from(ft[T, U]())

  trait Unapply[X]:
    type F[_,_]

  object Unapply:
    given unapply[G[_,_]]: (Unapply[∀∀[G]] {type F[A, B] = G[A, B]}) = new Unapply[∀∀[G]]:
      type F[A, B] = G[A, B]
}

private[exo] object Forall2Impl extends Forall2Module:
  type Forall2[F[_,_]] = F[Any, Any]
  def specialize[F[_,_], A, B](f: ∀∀[F]): F[A, B] = f.asInstanceOf[F[A, B]]
  def instantiation[F[_,_], A, B]: ∀∀[F] <~< F[A, B] = As.refl[(Any, Any)].asInstanceOf[∀∀[F] <~< F[A, B]]
  def monotonicity[F[_,_], G[_,_]](ev: ∀∀[[a, b] =>> F[a, b] <~< G[a, b]]): ∀∀[F] <~< ∀∀[G] =
    As.refl[(Any, Any)].asInstanceOf[∀∀[F] <~< ∀∀[G]]
  def from[F[_,_]](p: Prototype[F]): ∀∀[F] = p[Any, Any]
  def of[F[_,_]]: MkForall2[F] = new MkForall2Impl[F]

object Forall2Module extends Forall2Functions:
  extension [F[_,_]](a: ∀∀[F])
    def of[A, B]: F[A, B] = Forall2.specialize(a)
    def apply[A, B]: F[A, B] = of[A, B]

private[exo] final class MkForall2Impl[F[_,_]](val dummy: Boolean = false) extends AnyVal with Forall2Impl.MkForall2[F]:
  type T = Any
  type U = Any
  def from(ft: F[T, U]): Forall2Impl.∀∀[F] = ft

trait Forall2Functions {
  extension[F[_, _], G[_, _]] (fg: F ~~> G)
    def run[A, B](fab: F[A, B]): G[A, B] = fg[A, B](fab)
    def $(f: ∀∀[F]): ∀∀[G] = ∀∀.of[G].from(run(f.apply))
    def andThen[H[_, _]](gh: G ~~> H): F ~~> H = ~~>[F, H]([A, B] => (fab: F[A, B]) => gh.run(fg.run(fab)))
    def compose[E[_, _]](ef: E ~~> F): E ~~> G = ef andThen fg
  extension[->[_, _], F[_,_], G[_,_]] (iso: IsoK2[->, F, G])
    def to:   ∀∀[[a, b] =>> F[a, b] -> G[a, b]] = ∀∀.of[[a, b] =>> F[a, b] -> G[a, b]].fromH([T, U] => () => iso[T, U].to)
    def from: ∀∀[[a, b] =>> G[a, b] -> F[a, b]] = ∀∀.of[[a, b] =>> G[a, b] -> F[a, b]].fromH([T, U] => () => iso[T, U].from)
    def flip: IsoK2[->, G, F] = ∀∀.mk[IsoK2[->, G, F]].fromH([T, U] => () => iso[T, U].flip)
    def andThen[H[_,_]](iso2: IsoK2[->, G, H])(using DummyImplicit): IsoK2[->, F, H] =
      ∀∀.mk[IsoK2[->, F, H]].fromH([T, U] => () => iso[T, U].andThen(iso2[T, U]))
}
