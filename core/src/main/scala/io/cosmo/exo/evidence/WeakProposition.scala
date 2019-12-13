package io.cosmo.exo.evidence

import cats.Eq
import io.cosmo.exo.evidence.internal.Unsafe
import io.estatico.newtype.ops._
import io.estatico.newtype.macros.newsubtype

trait WeakProposition[A] {
  def equal[X : InhabitedSubset[*, A], Y: InhabitedSubset[*, A]]: X === Y =
    Unsafe.is[X, Y]

  def contractible(implicit A: ¬¬[A]): Contractible[A] =
    Contractible.witness[A](A, this)
}
object WeakProposition {
  def apply[A](implicit A: WeakProposition[A]): WeakProposition[A] = A

  // This covers Unit & other terminal objects.
  implicit def singleton[A <: Singleton]: WeakProposition[A] = new WeakProposition[A] { }
  implicit def unit: WeakProposition[Unit] = new WeakProposition[Unit] { }

  // All values are equal.
  implicit def eq[A](implicit prop: WeakProposition[A]): Eq[A] = Eq.allEqual[A]

  // Proposition
  implicit def prop[A](implicit prop: WeakProposition[A]): Proposition[WeakProposition[A]] =
    (_: Inhabited[WeakProposition[A]]) => prop
}

final case class InhabitedSubset[A, +B](conformity: A <~< B, inhabitance: Inhabited[A])
