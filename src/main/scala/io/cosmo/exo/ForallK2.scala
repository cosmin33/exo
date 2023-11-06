package io.cosmo.exo

import io.cosmo.exo.evidence.*

val ForallK2: ForallK2Module = ForallK2Impl
val ∀~~ : ForallK2.type = ForallK2
type ForallK2[A[_[_,_]]] = ForallK2.ForallK2[A]
type ∀~~[A[_[_,_]]] = ForallK2.ForallK2[A]

private[exo] sealed trait ForallK2Module:
  type ForallK2[Alg[_[_,_]]]
  type ∀~~[Alg[_[_,_]]] = ForallK2[Alg]

  trait Prototype[Alg[_[_,_]]]:
    def apply[F[_,_]]: Alg[F]
    final def make: ∀~~[Alg] = from(this)

  def specialize[Alg[_[_,_]], F[_,_]](v: ∀~~[Alg]): Alg[F]
  def instantiation[Alg[_[_,_]], F[_,_]]: ∀~~[Alg] <~< Alg[F]
  def monotonicity[A1[_[_,_]], B1[_[_,_]]](ev: ∀~~[[f[_,_]] =>> A1[f] <~< B1[f]]): ∀~~[A1] <~< ∀~~[B1]
  def from[Alg[_[_,_]]](p: Prototype[Alg]): ∀~~[Alg]
  def of[Alg[_[_,_]]]: MkForallK2[Alg]
  def mk[x](using u: Unapply[x]): MkForallK2[u.A] = of[u.A]

  trait MkForallK2[Alg[_[_,_]]] extends Any:
    type T[_,_]
    def from(ft: Alg[T]): ∀~~[Alg]
    def apply(ft: Alg[T]): ∀~~[Alg] = from(ft)
    def fromH(ft: [F[_,_]] => () => Alg[F]): ForallK2[Alg] = from(ft[T]())

  trait Unapply[X]:
    type A[_[_,_]]

  object Unapply:
    given unapply[B[_[_,_]]]: Unapply[∀~~[B]] {type A[f[_,_]] = B[f]} =
      new Unapply[∀~~[B]] { type A[f[_,_]] = B[f] }

end ForallK2Module

private[exo] object ForallK2Impl extends ForallK2Module:
  type ForallK2[A[_[_,_]]] = A[[α, β] =>> Any]
  def specialize[Alg[_[_,_]], F[_,_]](f: ∀~~[Alg]): Alg[F] = f.asInstanceOf[Alg[F]]
  def instantiation[Alg[_[_,_]], F[_,_]]: ∀~~[Alg] <~< Alg[F] = As.refl[Any].asInstanceOf[∀~~[Alg] <~< Alg[F]]
  def monotonicity[A1[_[_,_]], B1[_[_,_]]](ev: ∀~~[[f[_,_]] =>> A1[f] <~< B1[f]]): ∀~~[A1] <~< ∀~~[B1] =
    As.refl[Any].asInstanceOf[∀~~[A1] <~< ∀~~[B1]]
  def from[Alg[_[_,_]]](p: Prototype[Alg]): ∀~~[Alg] = p[[α, β] =>> Any]
  def of[Alg[_[_,_]]]: MkForallK2[Alg] = new MkForallK2Impl[Alg]

private[exo] final class MkForallK2Impl[Alg[_[_,_]]](val dummy: Boolean = false) extends AnyVal with ForallK2Impl.MkForallK2[Alg]:
  type T[α, β] = Any
  def from(ft: Alg[T]): ForallK2Impl.∀~~[Alg] = ft

object ForallK2Module:
  extension[Alg[_[_,_]]](a: ∀~~[Alg])
    def of[F[_,_]]: Alg[F] = ForallK2.specialize(a)
    def apply[F[_,_]]: Alg[F] = of[F]
