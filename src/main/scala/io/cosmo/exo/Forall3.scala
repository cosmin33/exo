package io.cosmo.exo

import io.cosmo.exo.evidence.*

val Forall3: Forall3Module = Forall3Impl
val ∀∀∀ : Forall3.type = Forall3
type Forall3[F[_,_,_]] = Forall3.Forall3[F]
type ∀∀∀[F[_,_,_]] = Forall3.Forall3[F]

private[exo] sealed trait Forall3Module:
  type Forall3[F[_,_,_]]
  type ∀∀∀[F[_,_,_]] = Forall3[F]

  trait Prototype[F[_,_,_]]:
    def apply[A, B, C]: F[A, B, C]
    final def make: ∀∀∀[F] = from(this)

  def specialize[F[_,_,_], A, B, C](f: ∀∀∀[F]): F[A, B, C]
  def instantiation[F[_,_,_], A, B, C]: ∀∀∀[F] <~< F[A, B, C]
  def monotonicity[F[_,_,_], G[_,_,_]](ev: ∀∀∀[[a, b, c] =>> F[a, b, c] <~< G[a, b, c]]): ∀∀∀[F] <~< ∀∀∀[G]
  def from[F[_,_,_]](p: Prototype[F]): ∀∀∀[F]
  def of[F[_,_,_]]: MkForall3[F]
  def apply[F[_,_,_]]: MkForall3[F] = of[F]
  def mk[X](using u: Unapply[X]): MkForall3[u.F] = of[u.F]

  sealed trait MkForall3[F[_,_,_]] extends Any:
    type A
    type B
    type C
    def from(ft: F[A, B, C]): ∀∀∀[F]
    def apply(ft: F[A, B, C]): ∀∀∀[F] = from(ft)
    def fromH(ft: [A, B, C] => () => F[A, B, C]): ∀∀∀[F] = from(ft[A, B, C]())

  trait Unapply[X]:
    type F[_,_,_]

  object Unapply:
    given unapply[G[_,_,_]]: (Unapply[∀∀∀[G]] {type F[A, B, C] = G[A, B, C]}) = new Unapply[∀∀∀[G]]:
      type F[A, B, C] = G[A, B, C]

private[exo] object Forall3Impl extends Forall3Module:
  type Forall3[F[_,_,_]] = F[Any, Any, Any]
  def specialize[F[_,_,_], A, B, C](f: ∀∀∀[F]): F[A, B, C] = f.asInstanceOf[F[A, B, C]]
  def instantiation[F[_,_,_], A, B, C]: ∀∀∀[F] <~< F[A, B, C] = As.refl[(Any, Any, Any)].asInstanceOf[∀∀∀[F] <~< F[A, B, C]]
  def monotonicity[F[_,_,_], G[_,_,_]](ev: ∀∀∀[[a, b, c] =>> F[a, b, c] <~< G[a, b, c]]): ∀∀∀[F] <~< ∀∀∀[G] =
    As.refl[(Any, Any, Any)].asInstanceOf[∀∀∀[F] <~< ∀∀∀[G]]
  def from[F[_,_,_]](p: Prototype[F]): ∀∀∀[F] = p[Any, Any, Any]
  def of[F[_,_,_]]: MkForall3[F] = new MkForall3Impl[F]

object Forall3Module:
  extension [F[_,_,_]](a: ∀∀∀[F])
    def of[A, B, C]: F[A, B, C] = Forall3.specialize(a)
    def apply[A, B, C]: F[A, B, C] = of[A, B, C]

private[exo] final class MkForall3Impl[F[_,_,_]](val dummy: Boolean = false) extends AnyVal with Forall3Impl.MkForall3[F]:
  type A = Any
  type B = Any
  type C = Any
  def from(ft: F[A, B, C]): Forall3Impl.∀∀∀[F] = ft
