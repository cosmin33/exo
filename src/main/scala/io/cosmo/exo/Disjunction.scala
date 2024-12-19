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

object Disjunction extends DisjunctionImplicits
  with DisjunctionInstances:

  def apply[L, R](e: Either[L, R]): \/[L, R] = e

  def left [L, R](l: L): \/[L, R] = Left(l)
  def right[L, R](r: R): \/[L, R] = Right(r)
  def swap[L, R](e: \/[L, R]): \/[R, L] = (e: Either[L, R]).swap

  def either[A, B, C](ac: A => C, bc: B => C): (A \/ B) => C = _.fold(ac, bc)

  /**  */
  def unsafeLeibniz: Either =~~= \/ = =~~=.refl

  given iso[L, R]: (Either[L, R] <=> (L \/ R)) = unsafeLeibniz.is[L, R].toIso
  
  given isoK2: (Either <~~> \/) = unsafeLeibniz.toIso

  given bifunctor: Endobifunctor[Function, \/] with
    def bimap[A, B, C, D](fab: A => B, fcd: C => D): (A \/ C) => (B \/ D) = _.bimap(fab, fcd)

  extension [A, B](e: A \/ B)
    def toEither: Either[A, B] = e
    def fold[X](f1: A => X, f2: B => X): X = e.toEither.fold(f1, f2)
    def bimap[C, D](f: A => C, g: B => D): C \/ D = e.fold(f(_).left, g(_).right)
  
  extension[A, B, C](e: A \/ (B \/ C))
    def toEither3: Either[A, Either[B, C]] = e
    def fold3[X](f1: A => X, f2: B => X, f3: C => X): X = e.fold(f1, _.fold(f2, f3))

  extension[A, B, C, D](e: A \/ (B \/ (C \/ D)))
    def toEither4: Either[A, Either[B, Either[C, D]]] = e
    def fold4[X](f1: A => X, f2: B => X, f3: C => X, f4: D => X): X = e.fold3(f1, f2, _.fold(f3, f4))

  extension[A, B, C, D, E](e: A \/ (B \/ (C \/ (D \/ E))))
    def toEither5: Either[A, Either[B, Either[C, Either[D, E]]]] = e
    def fold5[X](f1: A => X, f2: B => X, f3: C => X, f4: D => X, f5: E => X): X = e.fold4(f1, f2, f3, _.fold(f4, f5))
    
  extension[A, B, C, D, E, F](e: A \/ (B \/ (C \/ (D \/ (E \/ F)))))
    def toEither6: Either[A, Either[B, Either[C, Either[D, Either[E, F]]]]] = e
    def fold6[X](f1: A => X, f2: B => X, f3: C => X, f4: D => X, f5: E => X, f6: F => X): X = e.fold5(f1, f2, f3, f4, _.fold(f5, f6))

end Disjunction

trait DisjunctionImplicits extends DisjunctionImplicits01:
  given primary[A, B](using a: A): \/[A, B] = \/.left(a)

trait DisjunctionImplicits01:
  given secondary[A, B](using b: B): \/[A, B] = \/.right(b)

trait DisjunctionInstances extends DisjunctionInstances01:
  given disjunctionTypeclassLeft[T[_], A, B](using L: LaxSemigroupal[\/, Function, \/, T], ta: T[A]): T[A \/ B] = L.product(-\/(ta))

trait DisjunctionInstances01:
  given disjunctionTypeclassRight[T[_], A, B](using L: LaxSemigroupal[\/, Function, \/, T], tb: T[B]): T[A \/ B] = L.product(\/-(tb))
