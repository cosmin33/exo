package io.cosmo.exo

import io.cosmo.exo.evidence.*

val ForallHK: ForallHKModule = ForallHKImpl
val ∀≈ : ForallHK.type = ForallHK
type ForallHK[A[_[_[_]]]] = ForallHK.ForallHK[A]
type ∀≈[A[_[_[_]]]] = ForallHK.ForallHK[A]

private[exo] sealed trait ForallHKModule:
  type ForallHK[Alg[_[_[_]]]]
  type ∀≈[Alg[_[_[_]]]] = ForallHK[Alg]

  trait Prototype[Alg[_[_[_]]]]:
    def apply[F[_[_]]]: Alg[F]
    final def make: ∀≈[Alg] = from(this)

  def specialize[Alg[_[_[_]]], F[_[_]]](v: ∀≈[Alg]): Alg[F]
  def instantiation[Alg[_[_[_]]], F[_[_]]]: ∀≈[Alg] <~< Alg[F]
  def monotonicity[A1[_[_[_]]], B1[_[_[_]]]](ev: ∀≈[[f[_[_]]] =>> A1[f] <~< B1[f]]): ∀≈[A1] <~< ∀≈[B1]
  def from[Alg[_[_[_]]]](p: Prototype[Alg]): ∀≈[Alg]
  def of[Alg[_[_[_]]]]: MkForallHK[Alg]
  def mk[x](using u: Unapply[x]): MkForallHK[u.A] = of[u.A]

  trait MkForallHK[Alg[_[_[_]]]] extends Any:
    type T[_[_]]
    def from(ft: Alg[T]): ∀≈[Alg]
    def apply(ft: Alg[T]): ∀≈[Alg] = from(ft)
    def fromH(ft: [F[_[_]]] => () => Alg[F]): ForallHK[Alg] = from(ft[T]())

  trait Unapply[X]:
    type A[_[_[_]]]

  object Unapply:
    given unapply[B[_[_[_]]]]: Unapply[∀≈[B]] {type A[f[_[_]]] = B[f]} = new Unapply[∀≈[B]] { type A[f[_[_]]] = B[f] }

end ForallHKModule

private[exo] object ForallHKImpl extends ForallHKModule:
  type ForallHK[A[_[_[_]]]] = A[[α[_]] =>> Any]
  def specialize[Alg[_[_[_]]], F[_[_]]](f: ∀≈[Alg]): Alg[F] = f.asInstanceOf[Alg[F]]
  def instantiation[Alg[_[_[_]]], F[_[_]]]: ∀≈[Alg] <~< Alg[F] = As.refl[Any].asInstanceOf[∀≈[Alg] <~< Alg[F]]
  def monotonicity[A1[_[_[_]]], B1[_[_[_]]]](ev: ∀≈[[f[_[_]]] =>> A1[f] <~< B1[f]]): ∀≈[A1] <~< ∀≈[B1] =
    As.refl[Any].asInstanceOf[∀≈[A1] <~< ∀≈[B1]]
  def from[Alg[_[_[_]]]](p: Prototype[Alg]): ∀≈[Alg] = p[[α[_]] =>> Any]
  def of[Alg[_[_[_]]]]: MkForallHK[Alg] = new MkForallHKImpl[Alg]

private[exo] final class MkForallHKImpl[Alg[_[_[_]]]](val dummy: Boolean = false) extends AnyVal with ForallHKImpl.MkForallHK[Alg]:
  type T[α[_]] = Any
  def from(ft: Alg[T]): ForallHKImpl.∀≈[Alg] = ft

object ForallHKModule:
  extension[Alg[_[_[_]]]](a: ∀≈[Alg])
    def of[F[_[_]]]: Alg[F] = ForallHK.specialize(a)
    def apply[F[_[_]]]: Alg[F] = of[F]
