package io.cosmo.exo

import io.cosmo.exo.evidence.*

val ForallK: ForallKModule = ForallKImpl
val ∀~ : ForallK.type = ForallK
type ForallK[A[_[_]]] = ForallK.ForallK[A]
type ∀~[A[_[_]]] = ForallK.ForallK[A]

private[exo] sealed trait ForallKModule:
  type ForallK[Alg[_[_]]]
  type ∀~[Alg[_[_]]] = ForallK[Alg]

  trait Prototype[Alg[_[_]]]:
    def apply[F[_]]: Alg[F]
    final def make: ∀~[Alg] = from(this)

  def specialize[Alg[_[_]], F[_]](v: ∀~[Alg]): Alg[F]
  def instantiation[Alg[_[_]], F[_]]: ∀~[Alg] <~< Alg[F]
  def monotonicity[A1[_[_]], B1[_[_]]](ev: ∀~[[f[_]] =>> A1[f] <~< B1[f]]): ∀~[A1] <~< ∀~[B1]
  def from[Alg[_[_]]](p: Prototype[Alg]): ∀~[Alg]
  def of[Alg[_[_]]]: MkForallK[Alg]
  def apply[Alg[_[_]]]: MkForallK[Alg] = of[Alg]
  def mk[x](using u: Unapply[x]): MkForallK[u.A] = of[u.A]

  trait MkForallK[Alg[_[_]]] extends Any:
    type T[_]
    def from(ft: Alg[T]): ∀~[Alg]
    def apply(ft: Alg[T]): ∀~[Alg] = from(ft)
    def fromH(ft: [F[_]] => () => Alg[F]): ForallK[Alg] = from(ft[T]())

  trait Unapply[X]:
    type A[_[_]]

  object Unapply:
    given unapply[B[_[_]]]: Unapply[∀~[B]] {type A[f[_]] = B[f]} = new Unapply[∀~[B]] { type A[f[_]] = B[f] }

end ForallKModule

private[exo] object ForallKImpl extends ForallKModule:
  type ForallK[A[_[_]]] = A[[α] =>> Any]
  def specialize[Alg[_[_]], F[_]](f: ∀~[Alg]): Alg[F] = f.asInstanceOf[Alg[F]]
  def instantiation[Alg[_[_]], F[_]]: ∀~[Alg] <~< Alg[F] = As.refl[Any].asInstanceOf[∀~[Alg] <~< Alg[F]]
  def monotonicity[A1[_[_]], B1[_[_]]](ev: ∀~[[f[_]] =>> A1[f] <~< B1[f]]): ∀~[A1] <~< ∀~[B1] =
    As.refl[Any].asInstanceOf[∀~[A1] <~< ∀~[B1]]
  def from[Alg[_[_]]](p: Prototype[Alg]): ∀~[Alg] = p[[α] =>> Any]
  def of[Alg[_[_]]]: MkForallK[Alg] = new MkForallKImpl[Alg]

private[exo] final class MkForallKImpl[Alg[_[_]]](val dummy: Boolean = false) extends AnyVal with ForallKImpl.MkForallK[Alg]:
  type T[α] = Any
  def from(ft: Alg[T]): ForallKImpl.∀~[Alg] = ft

object ForallKModule:
  extension[Alg[_[_]]](a: ∀~[Alg])
    def of[F[_]]: Alg[F] = ForallK.specialize(a)
    def apply[F[_]]: Alg[F] = of[F]
  extension[F[_[_]], G[_[_]]](fg: F ≈> G)
    def run[A[_]](fa: F[A]): G[A] = fg[A](fa)
    def $(f: ∀~[F]): ∀~[G] = ∀~.of[G].from(run(f.apply))
    def andThen[H[_[_]]](gh: G ≈> H): F ≈> H = ≈>[F, H]([T[_]] => (ft: F[T]) => gh.run(fg.run(ft)))
    def compose[E[_[_]]](ef: E ≈> F): E ≈> G = ef andThen fg
//  extension[->[_,_], F[_[_]], G[_[_]]](iso: IsoH[->, F, G])
//    def to:   ∀~[[a[_]] =>> F[a] -> G[a]] = ∀~.of[[a[_]] =>> F[a] -> G[a]].fromH([T[_]] => () => iso[T].to)
//    def from: ∀~[[a[_]] =>> G[a] -> F[a]] = ∀~.of[[a[_]] =>> G[a] -> F[a]].fromH([T[_]] => () => iso[T].from)
//    def flip: IsoH[->, G, F] = ∀~.mk[IsoH[->, G, F]].fromH([T[_]] => () => iso[T].flip)
//    def andThen[H[_[_]]](iso2: IsoH[->, G, H])(using DummyImplicit): IsoH[->, F, H] =
//      ∀~.mk[IsoH[->, F, H]].fromH([T[_]] => () => iso[T].andThen(iso2[T]))
