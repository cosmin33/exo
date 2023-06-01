package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.Unsafe
import io.cosmo.exo.syntax.*
import io.cosmo.exo.functors.*

opaque type Disjunction[A, B] >: Either[A, B] = Either[A, B]

type \/[A, B] = Disjunction[A, B]
val \/ = Disjunction
def -\/[L, R](l: L): \/[L, R] = \/.left(l)
def \/-[L, R](r: R): \/[L, R] = \/.right(r)

object Disjunction extends DisjunctionImplicits {
  def apply[L, R](e: Either[L, R]): \/[L, R] = e

  def fold[A, B, X](e: \/[A, B])(f1: A => X, f2: B => X): X = (e: Either[A, B]).fold(f1, f2)
  def fold3[A, B, C, X](e: A \/ B \/ C)(f1: A => X, f2: B => X, f3: C => X): X = e.fold(_.fold(f1, f2), f3)
  def fold4[A, B, C, D, X](e: A \/ B \/ C \/ D)(f1: A => X, f2: B => X, f3: C => X, f4: D => X): X = e.fold(_.fold(_.fold(f1, f2), f3), f4)

  def left [L, R](l: L): \/[L, R] = Left(l)
  def right[L, R](r: R): \/[L, R] = Right(r)
  def swap[L, R](e: \/[L, R]): \/[R, L] = (e: Either[L, R]).swap

  def either[A, B, C](ac: A => C, bc: B => C): (A \/ B) => C = _.fold(ac, bc)

  def unsafeLeibniz: Either =~~= \/ = =~~=.refl

  def iso[L, R]: Either[L, R] <=> (L \/ R) = unsafeLeibniz.is[L, R].toIso
  
  def isoK2: Either <~~> \/ = unsafeLeibniz.toIso

  given bifunctor: Endobifunctor[Function, \/] with
    def bimap[A, B, C, D](fab: A => B, fcd: C => D): (A \/ C) => (B \/ D) = _.bimap(fab, fcd)
}

extension [A, B](e: A \/ B)
  def toEither: Either[A, B] = e
  def fold[X](f1: A => X, f2: B => X): X = Disjunction.fold(e)(f1, f2)
  def bimap[C, D](f: A => C, g: B => D): C \/ D = e.fold(a => f(a).left, b => g(b).right)

extension[A, B, C](e: A \/ B \/ C)
  def toEither3: Either[Either[A, B], C] = e
  def fold3[X](f1: A => X, f2: B => X, f3: C => X): X = Disjunction.fold3(e)(f1, f2, f3)

extension[A, B, C, D](e: A \/ B \/ C \/ D)
  def toEither4: Either[Either[Either[A, B], C], D] = e
  def fold4[X](f1: A => X, f2: B => X, f3: C => X, f4: D => X): X = Disjunction.fold4(e)(f1, f2, f3, f4)

trait DisjunctionImplicits extends DisjunctionImplicits01:
  given primary[A, B](using a: A): \/[A, B] = \/.left(a)

trait DisjunctionImplicits01:
  given secondary[A, B](using b: B): \/[A, B] = \/.right(b)

