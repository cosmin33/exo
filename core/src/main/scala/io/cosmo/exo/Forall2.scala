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

object Forall2Module:
  extension [F[_,_]](a: ∀∀[F])
    def of[A, B]: F[A, B] = Forall2.specialize(a)
    def apply[A, B]: F[A, B] = of[A, B]

private[exo] final class MkForall2Impl[F[_,_]](val dummy: Boolean = false) extends AnyVal with Forall2Impl.MkForall2[F]:
  type T = Any
  type U = Any
  def from(ft: F[T, U]): Forall2Impl.∀∀[F] = ft
