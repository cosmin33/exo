package io.cosmo.exo

import cats.Bifunctor
import cats.implicits._
import io.cosmo.exo.evidence.{=~~=, IsK2}
import io.estatico.newtype.Coercible

trait DisjunctionModule {
  type Type [L, R]
  type TypeL[L, R] <: Type[L, R]
  type TypeR[L, R] <: Type[L, R]

  def isK2: Either =~~= Type
  def bifunctor: Bifunctor[Type]

  def fold[L, R, A](d: Type[L, R])(la: L => A, ra: R => A): A
  def left [L, R](l: L): TypeL[L, R]
  def right[L, R](r: R): TypeR[L, R]
  def swap[L, R](d: Type[L, R]): Type[R, L]

  final def apply[L, R](e: Either[L, R]): Type[L, R] = isK2.is[L, R](e)
  final def iso[L, R]: Either[L, R] <=> Type[L, R] = isK2.is[L, R].toIso
  final def either[A, B, C](ac: A => C, bc: B => C): Type[A, B] => C = fold(_)(ac, bc)
}

private[exo] object DisjunctionModuleImpl extends DisjunctionModule {
  type Type[L, R] = Either[L, R]
  type TypeL[L, R] = Left[L, R]
  type TypeR[L, R] = Right[L, R]
  def isK2 = IsK2.refl
  def bifunctor = implicitly
  def fold[L, R, A](d: Either[L, R])(la: L => A, ra: R => A) = d.fold(la, ra)
  def left[L, R](l: L) = Left(l)
  def right[L, R](r: R) = Right(r)
  def swap[L, R](d: Either[L, R]) = d.swap
}

object DisjunctionModule extends DisjunctionModule01 {
  implicit class DisjunctionOps[L, R](value: L \/ R) {
    def fold[A](la: L => A, ra: R => A): A = \/.fold(value)(la, ra)
    def swap: R \/ L = \/.swap(value)
  }

  implicit val co: Coercible[∀∀[Either], ∀∀[\/]] = Coercible.instance

  implicit def primary[A, B](implicit a: A): A \/ B = -\/(a)
}
trait DisjunctionModule01 {
  implicit def secondary[A, B](implicit b: => B): A \/ B = \/-(b)
}

trait DisjunctionSyntax {
  implicit final class ToDisjunctionOps[A](a: A) {
    def left [B]: A \/ B = -\/(a)
    def right[B]: B \/ A = \/-(a)
  }

  implicit final class EitherAsDisjunction[A, B](ab: Either[A, B]) {
    def asDisjunction: A \/ B = \/(ab)
  }
}

trait DisjunctionFunctions {
  @inline def left [L, R](value: L): \/[L, R] = -\/(value)
  @inline def right[L, R](value: R): \/[L, R] = \/-(value)

  def either[A, B, C](ac: A => C)(bc: B => C): A \/ B => C = _.fold(ac, bc)
}

