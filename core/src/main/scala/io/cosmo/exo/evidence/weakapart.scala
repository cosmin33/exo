package io.cosmo.exo.evidence

import io.cosmo.exo.evidence.variance.IsConstant
import io.cosmo.exo._
import io.estatico.newtype.ops._
import io.estatico.newtype.macros.newsubtype
import cats.implicits._

import scala.language.experimental.macros

object weakapart {
  /**
   * In constructive mathematics, an apartness relation is a constructive
   * form of inequality, and is often taken to be more basic than equality.
   * It is often written as # to distinguish from the negation of equality
   * (the denial inequality) ≠, which is weaker.
   *
   * An apartness relation is a symmetric irreflexive binary relation with
   * the additional condition that if two elements are apart, then any other
   * element is apart from at least one of them (this last property is often
   * called co-transitivity or comparison).
   *
   * @see [[https://en.wikipedia.org/wiki/Apartness_relation
   *        Apartness relation]]
   */
  @newsubtype class WeakApart[A, B](val run: (A === B) => Void) {

    /**
     * Having `A === B` and `A =!= B` at the same time leads to a contradiction.
     */
    def contradicts(ab: A === B): Void = run(ab)

    /**
     * If `F[A]` equals to `F[B]` for unequal types `A` and `B`,
     * then `F` must be a constant type constructor.
     */
    def constant[F[_]](f: F[A] === F[B]): IsConstant[F] = IsConstant.witness1[F, A, B](this, f)

    def lower[F[_]]: WeakApart.PartialLower[F, A, B] = new WeakApart.PartialLower[F, A, B](this)

    /**
     * Inequality is a co-transitive relation: if two elements
     * are apart, then any other element is apart from at least
     * one of them.
     */
    def compare[C]: ¬¬[(A =!= C) \/ (B =!= C)] = {
      val f: (A === C, B === C) => Void = (ac, bc) => run.apply(ac andThen bc.flip)
      ¬¬.and(f).map(e => \/.bifunctor.bimap(e)(WeakApart.witness, WeakApart.witness))
    }

    def compareE[C]: ¬¬[Either[A =!= C, B =!= C]] = {
      val f: (A === C, B === C) => Void = (ac, bc) => run.apply(ac andThen bc.flip)
      ¬¬.andE(f).map(_.bimap(WeakApart.witness, WeakApart.witness))
    }

    /**
     * Inequality is symmetric relation and therefore can be flipped around.
     * Flipping is its own inverse, so `x.flip.flip == x`.
     */
    def flip: B =!= A = WeakApart.witness[B, A](ba => run(ba.flip))

    /**
     * Strengthen the proof by providing explicit type descriptions.
     */
    def strengthen(implicit A: TypeId[A], B: TypeId[B]): Apart[A, B] =
      Apart.witness(this, A, B)

    /**
     * Given an injective [[F]], if `A ≠ B`, then `F[A] ≠ F[B]`.
     */
    def lift[F[_]](implicit F: IsInjective[F]): F[A] =!= F[B] =
      WeakApart.witness[F[A], F[B]](p => contradicts(F(p)))

    /**
     * Classical proof that
     * ¬(a ~ b) ⟺ a ≸ b ⋁ b < a ⋁ a < b
     */
    def decompose: ¬¬[(B </< A) \/ (A </< B) \/ (A >~< B)] =
      ¬¬.lem[A <~< B].flatMap {
        _.fold(
          notLTE => ¬¬.lem[B <~< A].map {
            _.fold(
              notGTE => \/-(Incomparable.witness(notLTE, notGTE)),
              gte => -\/(-\/(StrictAs.witness(flip, gte)))
            )
          },
          lte => ¬¬.value(-\/(\/-(StrictAs.witness(this, lte))))
        )
      }
  }
  object WeakApart {
    def apply[A, B](implicit ev: WeakApart[A, B]): WeakApart[A, B] = ev

    def witness[A, B](fn: (A === B) => Void): A =!= B = fn.coerce

    implicit def isoCanonic[A, B]: ((A === B) => Void) <=> (A =!= B) = Iso.unsafeT(witness, _.run)

    implicit def proposition[A, B]: Proposition[A =!= B] =
      Proposition.negation[A === B].isomap(Iso.unsafeT(x => WeakApart.witness(x.run), x => ¬.witness(x.run)))

    implicit def inhabited[A, B](implicit A: ¬¬[A === B]): ¬[A =!= B] =
      ¬.witness(nab => A.contradicts(ab => nab.contradicts(ab)))

    implicit def uninhabited[A, B](implicit na: ¬[A === B]): ¬¬[A =!= B] =
      ¬¬.value(witness(na.contradicts))

    implicit def mkWeakApart[A, B]: A =!= B = macro internal.MacroUtil.mkWeakApart[A, B]

    /**
     * Inequality is an irreflexive relation.
     */
    def irreflexive[A](ev: A =!= A): Void = ev.contradicts(Is.refl[A])

    private[WeakApart] final class PartialLower[F[_], A, B](val ab: =!=[A, B]) extends AnyVal {
      def apply[X, Y](implicit A: A === F[X], B: B === F[Y]): X =!= Y =
        WeakApart.witness(xy => ab(A andThen xy.lift[F] andThen B.flip))
    }
  }

}
