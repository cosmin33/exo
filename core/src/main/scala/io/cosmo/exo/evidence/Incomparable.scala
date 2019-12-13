package io.cosmo.exo.evidence

import cats.implicits._
import io.cosmo.exo._


final case class Incomparable[A, B](notLessOrEqual: ¬[A <~< B], notGreaterOrEqual: ¬[B <~< A]) { ab =>
  import Incomparable._

  def notEqual   :   A =!= B  = WeakApart.witness(equal => notLessOrEqual.run(equal.toAs))
  def notLess    : ¬[A </< B] = Uninhabited.witness(ineq => notLessOrEqual.run(ineq.conformity))
  def notGreater : ¬[B </< A] = Uninhabited.witness(ineq => notGreaterOrEqual.run(ineq.conformity))

  def lift[F[_]](implicit F: IsInjective[F]): F[A] >~< F[B] = F.incomparable[A, B](ab)

  def flip: B >~< A = witness(notGreaterOrEqual, notLessOrEqual)
}
object Incomparable {
  type Canonic[A, B] = (¬[A <~< B], ¬[B <~< A])

  def witness[A, B](notBelow: ¬[A <~< B], notAbove: ¬[B <~< A]): Incomparable[A, B] =
    new Incomparable[A, B](notBelow, notAbove)

  implicit def isoCanonic[A, B]: Canonic[A, B]  <=> (A >~< B) =
    Iso.unsafeT({case (nb, na) => witness(nb, na)}, c => (c.notLessOrEqual, c.notGreaterOrEqual))

  /**
   * a ≸ b ⟺ ¬(a ~ b) ⋀ ¬(a < b) ⋀ ¬(b < a)
   */
  def witness1[A, B](notEqual: A =!= B, notLess: ¬[A </< B], notGreater: ¬[B </< A]): A >~< B =
    notEqual.decompose.map {
      _.fold(
        _.fold(notGreater.run, notLess.run),
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
    Uninhabited.witness(ab => ev.run(_.fold(ab.notGreaterOrEqual.run, ab.notLessOrEqual.run)))

  def witnessNotE[A, B](ev: ¬¬[(B <~< A) Either (A <~< B)]): ¬[A >~< B] =
    Uninhabited.witness(ab => ev.run(_.fold(ab.notGreaterOrEqual.run, ab.notLessOrEqual.run)))

  def irreflexive[A](ev: A >~< A): Void = ev.notEqual(Is.refl)

  implicit def proposition[A, B]: Proposition[Incomparable[A, B]] =
    (Proposition[¬[A <~< B]] zip Proposition[¬[B <~< A]]).isomap(Iso.unsafeT(
      p => witness(p._1, p._2),
      p => (p.notLessOrEqual, p.notGreaterOrEqual)
    ))
}
