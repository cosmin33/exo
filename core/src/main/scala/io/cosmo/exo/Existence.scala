package io.cosmo.exo

import cats.~>

import scala.language.{existentials, implicitConversions, reflectiveCalls}

trait Existence {
  import ExistenceHelpers._

  type ExistsK1[F[_]]          = K1Mod.type#Type[F]
  type ExistsK11[F[_,_]]       = K11Mod.type#Type[F]
  type ExistsK2[T[_[_]]]       = K2Mod.type#Type[T]
  type ExistsK21[T[_[_],_]]    = K21Mod.type#Type[T]
  type ExistsK211[T[_[_],_,_]] = K211Mod.type#Type[T]
  type ExistsK3[T[_[_[_]]]]    = K3Mod.type#Type[T]
  val  ExistsK1:   K1Mod.type   = K1Mod
  val  ExistsK11:  K11Mod.type  = K11Mod
  val  ExistsK2:   K2Mod.type   = K2Mod
  val  ExistsK21:  K21Mod.type  = K21Mod
  val  ExistsK211: K211Mod.type = K211Mod
  val  ExistsK3:   K3Mod.type   = K3Mod
  type ∃[F[_]] = ExistsK1[F]
  val  ∃ = K1Mod
}

object Existence extends Existence

private[exo] object ExistenceHelpers {

  sealed trait ExistsTag { sealed trait Tag extends Any }
  trait K1Mod   { type Type[+F[_]]        <: (Any {type A})                    with   K1Mod.Tag }
  trait K11Mod  { type Type[+F[_,_]]      <: (Any {type A; type B})            with  K11Mod.Tag }
  trait K2Mod   { type Type[+L[_[_]]]     <: (Any {type F[_]})                 with   K2Mod.Tag }
  trait K21Mod  { type Type[+L[_[_],_]]   <: (Any {type F[_]; type A})         with  K21Mod.Tag }
  trait K211Mod { type Type[+L[_[_],_,_]] <: (Any {type F[_]; type A; type B}) with K211Mod.Tag }
  trait K3Mod   { type Type[+L[_[_[_]]]]  <: (Any {type M[_[_]]})              with   K3Mod.Tag }

  object K1Mod extends K1Mod with ExistsTag {
    def apply[F[_]]: Partial[F] = new Partial[F] 
    final class Partial[F[_]] { @inline def apply[X](x: F[X]): Type[F] = wrap(x) }
    def apply  [F[_], A](t: F[A]): Type[F] = wrap[F, A](t)
    def wrap   [F[_], A](t: F[A]): Type[F] = t.asInstanceOf[Type[F]]
    def unapply[F[_]]   (t: Type[F]): Option[F[t.A]] = Some(unwrap(t))
    def unwrap [F[_]]   (t: Type[F]): F[t.A] = t.asInstanceOf[F[t.A]]
    def mapK[F[_], G[_]](tf: Type[F])(fg: F ~> G): Type[G] = wrap(fg.apply(unwrap(tf)))
    implicit final def toExistsK1Ops[F[_]](fa: ExistsK1[F]): ExistsK1Ops[F, fa.A] = new ExistsK1Ops[F, fa.A](fa)
  }
  object K11Mod extends K11Mod with ExistsTag {
    def apply[F[_,_]]: Partial[F] = new Partial[F]
    final class Partial[F[_,_]] { @inline def apply[X, Y](x: F[X, Y]): Type[F] = wrap(x) }
    def apply  [F[_,_], A, B](t: F[A, B]): Type[F] = wrap[F, A, B](t)
    def wrap   [F[_,_], A, B](t: F[A, B]): Type[F] = t.asInstanceOf[Type[F]]
    def unapply[F[_,_]]      (t: Type[F]): Option[F[t.A, t.B]] = Some(unwrap(t))
    def unwrap [F[_,_]]      (t: Type[F]): F[t.A, t.B] = t.asInstanceOf[F[t.A, t.B]]
    implicit final def toExistsK11Ops[F[_,_]](fa: ExistsK11[F]): ExistsK11Ops[F, fa.A, fa.B] = new ExistsK11Ops[F, fa.A, fa.B](fa)
  }
  object K2Mod extends K2Mod with ExistsTag {
    def apply[L[_[_]]]: Partial[L] = new Partial[L]
    final class Partial[L[_[_]]] { @inline def apply[F[_]](x: L[F]): Type[L] = wrap(x) }
    def apply  [L[_[_]], F[_]](t: L[F]): Type[L] = wrap[L, F](t)
    def wrap   [L[_[_]], F[_]](t: L[F]): Type[L] = t.asInstanceOf[Type[L]]
    def unapply[L[_[_]], F[_]](t: Type[L]): Option[L[t.F]] = Some(unwrap(t))
    def unwrap [L[_[_]], F[_]](t: Type[L]): L[t.F] = t.asInstanceOf[L[t.F]]
    implicit final def toExistsK2Ops[L[_[_]]](fa: ExistsK2[L]): ExistsK2Ops[L, fa.F] = new ExistsK2Ops[L, fa.F](fa)
  }
  object K21Mod extends K21Mod with ExistsTag {
    def apply[L[_[_],_]]: Partial[L] = new Partial[L]
    final class Partial[L[_[_],_]] { @inline def apply[F[_], X](x: L[F, X]): Type[L] = wrap(x) }
    def apply  [L[_[_],_], F[_], A](t: L[F, A]): Type[L] = wrap[L, F, A](t)
    def wrap   [L[_[_],_], F[_], A](t: L[F, A]): Type[L] = t.asInstanceOf[Type[L]]
    def unapply[L[_[_],_], F[_], A](t: Type[L]): Option[L[t.F, t.A]] = Some(unwrap(t))
    def unwrap [L[_[_],_], F[_], A](t: Type[L]): L[t.F, t.A] = t.asInstanceOf[L[t.F, t.A]]
    implicit final def toExistsK21Ops[L[_[_],_]](fa: ExistsK21[L]): ExistsK21Ops[L, fa.F, fa.A] = new ExistsK21Ops[L, fa.F, fa.A](fa)
  }
  object K211Mod extends K211Mod with ExistsTag {
    def apply[L[_[_],_,_]]: Partial[L] = new Partial[L]
    final class Partial[L[_[_],_,_]] { @inline def apply[F[_], X, Y](x: L[F, X, Y]): Type[L] = wrap(x) }
    def apply  [L[_[_],_,_], F[_], A, B](t: L[F, A, B]): Type[L] = wrap[L, F, A, B](t)
    def wrap   [L[_[_],_,_], F[_], A, B](t: L[F, A, B]): Type[L] = t.asInstanceOf[Type[L]]
    def unapply[L[_[_],_,_], F[_], A, B](t: Type[L]): Option[L[t.F, t.A, t.B]] = Some(unwrap(t))
    def unwrap [L[_[_],_,_], F[_], A, B](t: Type[L]): L[t.F, t.A, t.B] = t.asInstanceOf[L[t.F, t.A, t.B]]
    implicit final def toExistsK211Ops[L[_[_],_,_]](fa: ExistsK211[L]): ExistsK211Ops[L, fa.F, fa.A, fa.B] = new ExistsK211Ops[L, fa.F, fa.A, fa.B](fa)
  }
  object K3Mod extends K3Mod with ExistsTag {
    def apply[L[_[_[_]]]]: Partial[L] = new Partial[L]
    final class Partial[L[_[_[_]]]] { @inline def apply[M[_[_]]](x: L[M]): Type[L] = wrap[L, M](x) }
    def apply  [L[_[_[_]]], F[_[_]]](t: L[F]): Type[L] = wrap[L, F](t)
    def wrap   [L[_[_[_]]], F[_[_]]](t: L[F]): Type[L] = t.asInstanceOf[Type[L]]
    def unapply[L[_[_[_]]], F[_[_]]](t: Type[L]): Option[L[t.M]] = Some(unwrap(t))
    def unwrap [L[_[_[_]]], F[_[_]]](t: Type[L]): L[t.M] = t.asInstanceOf[L[t.M]]
    implicit final def toExistsK3Ops[L[_[_[_]]]](fa: ExistsK3[L]): ExistsK3Ops[L, fa.M] = new ExistsK3Ops[L, fa.M](fa)
  }

  final class ExistsK1Ops[F[_], X](val fa: ExistsK1[F] { type A = X }) extends AnyVal {
    def value: F[X] = K1Mod.unwrap(fa)
    def mapK[G[_]](fg: F ~> G): ∃[G] = K1Mod.mapK[F, G](fa)(fg)
    def toScala: F[X] forSome { type X } = K1Mod.unwrap[F](fa)
  }
  final class ExistsK11Ops[F[_,_], X, Y](val fa: ExistsK11[F] { type A = X; type B = Y }) extends AnyVal {
    def value: F[X, Y] = K11Mod.unwrap(fa)
  }
  final class ExistsK2Ops[L[_[_]], J[_]](val fa: ExistsK2[L] { type F[ᵒ] = J[ᵒ] }) extends AnyVal {
    def value: L[J] = K2Mod.unwrap(fa)
  }
  final class ExistsK21Ops[L[_[_],_], J[_], X](val fa: ExistsK21[L] { type F[ᵒ] = J[ᵒ]; type A = X }) extends AnyVal {
    def value: L[J, X] = K21Mod.unwrap(fa)
  }
  final class ExistsK211Ops[L[_[_],_,_], J[_], X, Y](val fa: ExistsK211[L] { type F[ᵒ] = J[ᵒ]; type A = X; type B = Y }) extends AnyVal {
    def value: L[J, X, Y] = K211Mod.unwrap(fa)
  }
  final class ExistsK3Ops[L[_[_[_]]], N[_[_]]](val fa: ExistsK3[L] { type M[ᵒ[_]] = N[ᵒ] }) extends AnyVal {
    def value: L[N] = K3Mod.unwrap(fa)
  }

}
