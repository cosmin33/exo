package io.cosmo.exo.inhabitance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.Unsafe

trait WeakProposition[A]:
  def equal[X : InhabitedSubset[*, A], Y: InhabitedSubset[*, A]]: X === Y = Unsafe.is[X, Y]
  def contractible(using A: ¬¬[A]): Contractible[A] = Contractible.witness[A](using A, this)

object WeakProposition {
  def apply[A](using A: WeakProposition[A]): WeakProposition[A] = A

  given singleton[A <: Singleton]: WeakProposition[A] = new WeakProposition[A] { }
  given unit: WeakProposition[Unit] = new WeakProposition[Unit] { }

  given prop[A](using prop: WeakProposition[A]): Proposition[WeakProposition[A]] =
    Proposition.witness[WeakProposition[A]](_ => prop)

}

final case class InhabitedSubset[A, +B](conformity: A <~< B, inhabitance: Inhabited[A])
