package io.cosmo.exo.evidence

import io.cosmo.exo.*
import io.cosmo.exo.variance.*
import io.cosmo.exo.internal.*
import io.cosmo.exo.inhabitance.*

import scala.util.NotGiven

class WeakApart[A, B](val run: (A === B) => Void) {

  /** Having `A === B` and `A =!= B` at the same time leads to a contradiction. */
  def contradicts(ab: A === B): Void = run(ab)

  /** If `F[A]` equals to `F[B]` for unequal types `A` and `B`, then `F` must be a constant type constructor. */
  def constant[F[_]](f: F[A] === F[B]): IsConstant[F] = IsConstant.witness1[F, A, B](this, f)

  def lower[F[_]]: WeakApart.PartialLower[F, A, B] = new WeakApart.PartialLower[F, A, B](this)

  /** Inequality is a co-transitive relation:
   * if two elements are apart, then any other element is apart from at least one of them. */
  def compare[C]: ¬¬[(A =!= C) \/ (B =!= C)] = {
    val f: (A === C, B === C) => Void = (ac, bc) => run.apply(ac andThen bc.flip)
    ¬¬.and(f).map(_.bimap(WeakApart.witness, WeakApart.witness))
  }

  def compareE[C]: ¬¬[Either[A =!= C, B =!= C]] = {
    val f: (A === C, B === C) => Void = (ac, bc) => run.apply(ac andThen bc.flip)
    ¬¬.andE(f).map(_.fold(l => Left(WeakApart.witness(l)), r => Right(WeakApart.witness(r))))
  }

  /** Inequality is symmetric relation and therefore can be flipped around.
   * Flipping is its own inverse, so `eq.flip.flip == eq`. */
  def flip: B =!= A = WeakApart.witness[B, A](ba => run(ba.flip))

  /** Given an injective [[F]], if `A ≠ B`, then `F[A] ≠ F[B]`. */
  def lift[F[_]](using F: IsInjective[F]): F[A] =!= F[B] =
    WeakApart.witness[F[A], F[B]](p => contradicts(F(p)))

  /** Classical proof that `¬(a ~ b) ⟺ a ≸ b ⋁ b < a ⋁ a < b` */
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

  def witness[A, B](fn: (A === B) => Void): A =!= B = new WeakApart[A, B](fn)

  given isoCanonic[A, B]: (((A === B) => Void) <=> (A =!= B)) = Iso.unsafe(witness, _.run)

  given proposition[A, B]: Proposition[A =!= B] =
    Proposition.negation[A === B].isomap(Iso.unsafe(x => WeakApart.witness(x), x => ¬.witness(x.run)))

  given inhabited[A, B](using A: ¬¬[A === B]): ¬[A =!= B] =
    ¬.witness(nab => A.contradicts(ab => nab.contradicts(ab)))

  given uninhabited[A, B](using na: ¬[A === B]): ¬¬[A =!= B] =
    ¬¬.value(witness(na.contradicts))

  /** Inequality is an irreflexive relation. */
  def irreflexive[A](ev: A =!= A): Void = ev.contradicts(Is.refl[A])

  private[WeakApart] final class PartialLower[F[_], A, B](val ab: =!=[A, B]) extends AnyVal {
    def apply[X, Y](implicit A: A === F[X], B: B === F[Y]): X =!= Y =
      WeakApart.witness(xy => ab.run(A andThen xy.lift[F] andThen B.flip))
  }

  given [A, B](using NotGiven[A === B]): (A =!= B) = Unsafe.weakApart[A, B]

  import scala.quoted._

//  inline given impl[A, B]: (A =!= B) = ${ impl1 }

  def impl1[A, B](using q: Quotes, ta: Type[A], tb: Type[B]): Expr[A =!= B] = {
    if (ta == tb) {
      throw AssertionError("Cannot prove that " + Type.show[A] + " =!= " + Type.show[B] + " because they are the same type")
    } else {
      '{ Unsafe.weakApart[A, B] }
    }
  }

}
