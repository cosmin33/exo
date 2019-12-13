package io.cosmo.exo

import cats.implicits._
import cats.Bifunctor
import io.cosmo.exo.evidence.{===, =~=, =~~=, Is, IsK, IsK2}
import io.estatico.newtype.Coercible

trait ConjunctionModule {
  type Type[L, R]

  def isK2: Tuple2 =~~= Type
  def bifunctor: Bifunctor[Type]

  def unfold[L, R, A](a: A)(al: A => L, ar: A => R): Type[L, R]
  def first [L, R](p: Type[L, R]): L
  def second[L, R](p: Type[L, R]): R
  def swap[L, R](p: Type[L, R]): Type[R, L]

  final def apply[L, R](p: (L, R)): Type[L, R] = isK2.is[L, R](p)
  final def apply[L, R](l: L, r: R): Type[L, R] = apply((l, r))
  final def iso[L, R]: (L, R) <=> Type[L, R] = isK2.is[L, R].toIso
  final def both[A, B, C](ab: A => B, ac: A => C): A => Type[B, C] = unfold(_)(ab, ac)
}

object ConjunctionModule {
  implicit class ConjunctionOps[L, R](value: L /\ R) {
    def _1: L = /\.first(value)
    def _2: R = /\.second(value)
    def swap: R /\ L = /\.swap(value)
  }

  implicit val co: Coercible[∀∀[Tuple2], ∀∀[/\]] = Coercible.instance

  implicit def bothImp[A, B](implicit a: A, b: B): A /\ B = /\(a, b)
}

private[exo] object ConjunctionModuleImpl extends ConjunctionModule {
  type Type[L, R] = (L, R)
  def isK2 = =~~=.refl
  def bifunctor = implicitly
  def unfold[L, R, A](a: A)(al: A => L, ar: A => R) = (al(a), ar(a))
  def first[L, R](p: (L, R)) = p._1
  def second[L, R](p: (L, R)) = p._2
  def swap[L, R](p: (L, R)) = p.swap
}

trait ConjunctionSyntax {
  implicit final class TupleAsConjunction[A, B](ab: (A, B)) {
    def asConjunction: A /\ B = /\(ab)
  }
}


trait ConjunctionFunctions {
  def both[A, B, C](ab: A => B)(ac: A => C): A => (B, C) = a => (ab(a), ac(a))
}

