package io.cosmo.exo.inhabitance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

final case class Contractible[A](inhabited: Inhabited[A], proposition: WeakProposition[A]):
  /** All inhabited subtypes of a contractible type are equal. */
  def contract[B](using p: B <~< A, B: Inhabited[B]): B === A =
    proposition.equal[B, A](InhabitedSubset(p, B), InhabitedSubset(As.refl[A], inhabited))

object Contractible:
  def apply[A](using A: Contractible[A]): Contractible[A] = A

  given isoCanonic[A]: <=>[(¬¬[A], WeakProposition[A]), Contractible[A]] =
    Iso.unsafe({ case (i, w) => witness(using i, w) }, c => (c.inhabited, c.proposition))

  given witness[A](using inhabited: ¬¬[A], proposition: WeakProposition[A]): Contractible[A] =
    Contractible[A](inhabited, proposition)

  given singleton[A <: Singleton](using A: ValueOf[A]): Contractible[A] =
    new Contractible[A](¬¬.value(A.value), Proposition.singleton[A])
