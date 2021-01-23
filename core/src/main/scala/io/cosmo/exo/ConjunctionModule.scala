package io.cosmo.exo

import cats.implicits._
import cats.Bifunctor
import io.cosmo.exo.categories.functors.{LaxMonoidal, LaxSemigroupal}
import io.cosmo.exo.evidence.{===, =~=, =~~=, Is, IsK, IsK2}
import io.estatico.newtype.Coercible

trait ConjunctionModule {
  type Type[L, R]

  def leibniz: Tuple2 =~~= Type
  def bifunctor: Bifunctor[Type]

  def unfold[L, R, A](a: A)(al: A => L, ar: A => R): Type[L, R]
  def unfold3[A, B, C, X](a: X)(f1: X => A, f2: X => B, f3: X => C): Type[A, Type[B, C]]
  def unfold4[A, B, C, D, X](a: X)(f1: X => A, f2: X => B, f3: X => C, f4: X => D): Type[A, Type[B, Type[C, D]]]
  def first [L, R](p: Type[L, R]): L
  def second[L, R](p: Type[L, R]): R
  def swap[L, R](p: Type[L, R]): Type[R, L]

  final def apply[L, R](p: (L, R)): Type[L, R] = leibniz.is[L, R](p)
  final def apply[L, R](l: L, r: R): Type[L, R] = apply((l, r))
  final def iso[L, R]: (L, R) <=> Type[L, R] = leibniz.is[L, R].toIso
  final def both[A, B, C](ab: A => B, ac: A => C): A => Type[B, C] = unfold(_)(ab, ac)
}

object ConjunctionModule {
  implicit class ConjunctionOps[L, R](value: L /\ R) {
    def _1: L = /\.first(value)
    def _2: R = /\.second(value)
    def swap: R /\ L = /\.swap(value)
    def tuple: (L, R) = /\.iso[L, R].flip(value)
  }

  implicit val co: Coercible[∀∀[Tuple2], ∀∀[/\]] = Coercible.instance

  implicit def iso[A, B]: (A, B) <=> (A /\ B) = /\.leibniz.is[A, B].toIso
  implicit val isoK2: (*, *) <~~> /\ = /\.leibniz.toIso

  implicit def bothImp[A, B](implicit a: A, b: B): A /\ B = /\(a, b)

  implicit def productTypeclass[T[_], A, B](implicit
    L: LaxSemigroupal.Endo[* => *, /\, T], ta: T[A], tb: T[B]
  ): T[A /\ B] = L.product(/\(ta, tb))

  def typeclassFromTuple[TC[_], A, B](implicit t: TC[(A, B)]): TC[A /\ B] =
    /\.leibniz.subst[λ[f[_,_] => TC[f[A, B]]]](t)
}

private[exo] object ConjunctionModuleImpl extends ConjunctionModule {
  type Type[L, R] = (L, R)
  def leibniz = =~~=.refl
  def bifunctor = implicitly
  def unfold[L, R, A](a: A)(al: A => L, ar: A => R) = (al(a), ar(a))
  def unfold3[X, Y, Z, A](a: A)(f1: A => X, f2: A => Y, f3: A => Z) = (f1(a), (f2(a), f3(a)))
  def unfold4[A, B, C, D, X](a: X)(f1: X => A, f2: X => B, f3: X => C, f4: X => D) = (f1(a), (f2(a), (f3(a), f4(a))))
  def first[L, R](p: (L, R)) = p._1
  def second[L, R](p: (L, R)) = p._2
  def swap[L, R](p: (L, R)) = p.swap
}

trait ConjunctionSyntax {
  implicit final class Tuple2AsConjunction[A, B](ab: (A, B)) {
    def asConjunction: A /\ B = /\(ab)
  }
  implicit final class Tuple3AsConjunction[A, B, C](abc: (A, B, C)) {
    def asConjunction3: A /\ B /\ C = /\(/\(abc._1, abc._2), abc._3)
  }
  implicit final class Tuple4AsConjunction[A, B, C, D](abc: (A, B, C, D)) {
    def asConjunction4: A /\ B /\ C /\ D = /\(/\(/\(abc._1, abc._2), abc._3), abc._4)
  }
  implicit final class Tuple5AsConjunction[A, B, C, D, E](abc: (A, B, C, D, E)) {
    def asConjunction5: A /\ B /\ C /\ D /\ E = /\(/\(/\(/\(abc._1, abc._2), abc._3), abc._4), abc._5)
  }
}


trait ConjunctionFunctions {
  def both[A, B, C](ab: A => B)(ac: A => C): A => (B, C) = a => (ab(a), ac(a))
}

