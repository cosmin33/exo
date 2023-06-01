package io.cosmo.exo.evidence

import io.cosmo.exo.*
import io.cosmo.exo.inhabitance.*

final case class Incomparable[A, B](notLessOrEqual: ¬[A <~< B], notGreaterOrEqual: ¬[B <~< A]) { ab =>
  import Incomparable._

  def notEqual   :   A =!= B  = WeakApart.witness(equal => notLessOrEqual(equal.toAs))
  def notLess    : ¬[A </< B] = Uninhabited.witness(ineq => notLessOrEqual(ineq.conformity))
  def notGreater : ¬[B </< A] = Uninhabited.witness(ineq => notGreaterOrEqual(ineq.conformity))

  def lift[F[_]](implicit F: IsInjective[F]): F[A] >~< F[B] = F.incomparable[A, B](ab)

  def flip: B >~< A = witness(notGreaterOrEqual, notLessOrEqual)
}
object Incomparable {
  def witness[A, B](notBelow: ¬[A <~< B], notAbove: ¬[B <~< A]): Incomparable[A, B] =
    new Incomparable[A, B](notBelow, notAbove)

  type Canonic[A, B] = (¬[A <~< B], ¬[B <~< A])

  implicit def isoCanonic[A, B]: Canonic[A, B]  <=> (A >~< B) =
    Iso.unsafe({case (nb, na) => witness(nb, na)}, c => (c.notLessOrEqual, c.notGreaterOrEqual))

  /**
   * a ≸ b ⟺ ¬(a ~ b) ⋀ ¬(a < b) ⋀ ¬(b < a)
   */
  def witness1[A, B](notEqual: A =!= B, notLess: ¬[A </< B], notGreater: ¬[B </< A]): A >~< B =
    notEqual.decompose.map {
      _.fold(
        _.fold(notGreater, notLess),
        ra => ra
      )
    }.proved

  /**
   * ¬(a ≸ b)
   * ⟺ ¬(¬(a ~ b) ⋀ ¬(a < b) ⋀ ¬(b < a))
   * ⟺ a ~ b ⋁ a < b ⋁ b < a
   * ⟺ a ≤ b ⋁ b ≤ b
   */
  def witnessNot[A, B](ev: ¬¬[(B <~< A) \/ (A <~< B)]): ¬[A >~< B] =
    Uninhabited.witness(ab => ev(_.fold(ab.notGreaterOrEqual, ab.notLessOrEqual)))

  def witnessNotE[A, B](ev: ¬¬[(B <~< A) Either (A <~< B)]): ¬[A >~< B] =
    Uninhabited.witness(ab => ev(_.fold(ab.notGreaterOrEqual, ab.notLessOrEqual)))

  def irreflexive[A](ev: A >~< A): Void = ev.notEqual.run(Is.refl)

  implicit def proposition[A, B]: Proposition[Incomparable[A, B]] =
    Proposition[¬[A <~< B]].zip[¬[B <~< A]].isomap(Iso.unsafe(
      p => witness(p._1, p._2),
      p => (p.notLessOrEqual, p.notGreaterOrEqual)
    ))
    
}
