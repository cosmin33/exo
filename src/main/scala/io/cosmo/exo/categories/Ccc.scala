package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.functors._
import io.cosmo.exo.syntax._

trait Ccc[->[_,_], ⊙[_,_]] extends Cartesian[->, ⊙] { self =>
  type |->[_,_] // Hom objects representation

  def curry  [A, B, C](f: (A ⊙ B) -> C): A -> (B |-> C)
  def uncurry[A, B, C](f: A -> (B |-> C)): (A ⊙ B) -> C

  private given Subcat.Aux[->, TC] = C

  def rcurry  [A: TC, B: TC, C](f: (A ⊙ B) -> C): B -> (A |-> C) = curry(swap[B, A] >>> f)
  def runcurry[A: TC, B: TC, C](f: B -> (A |-> C)): (A ⊙ B) -> C = swap[A, B] >>> uncurry(f)

  def apply  [A, B](using t: TC[A |-> B]): ⊙[A |-> B, A] -> B = uncurry(C.id[A |-> B])
  def unapply[A, B](using t: TC[A ⊙ B]): A -> (B |-> (A ⊙ B)) = curry(C.id[A ⊙ B])

  def const[A: TC, B: TC, C](f: B -> C): A -> (B |-> C) = curry(snd[A, B] >>> f)

  def thing[A: TC, B: TC](in: Id -> (A |-> B)): A -> B = coidl[A] >>> uncurry(in)

  /** Iso between `Id -> (A |-> B)` and `A -> B` */
  def isoConstThing[A: TC, B: TC](using term: Terminal.Aux[->, TC, Id]): (Id -> (A |-> B)) <=> (A -> B) =
    Iso.unsafe(thing[A, B](_), const(_)(using term.TC, summon))

  def precmp [A: TC, B, C: TC](f: A -> B)(using t: TC[C |-> A]): (C |-> A) -> (C |-> B) = curry(apply[C, A] >>> f)
  def postcmp[A: TC, B: TC, C: TC](f: A -> B)(using t: TC[B |-> C]): (B |-> C) -> (A |-> C) =
    curry(grouped(C.id[B |-> C], f) >>> apply[B, C])

  def promap1[A: TC, B, C: TC, D: TC](f: A -> B, g: C -> D)(using tca: TC[C |-> A], tda: TC[D |-> A]): (D |-> A) -> (C |-> B) =
    postcmp[C, D, A](g) >>> precmp[A, B, C](f)
  def promap2[A: TC, B: TC, C: TC, D](f: A -> B, g: C -> D)(using tac: TC[A |-> C], tbc: TC[B |-> C]): (B |-> C) -> (A |-> D) =
    promap1(g, f)

  // Cartesian Closed Functor Laws: (to be deleted once I code the functor)
  // F(B -> A) => F(B) -> F(A)
  // F(B -> A) ⊙ F(B) <=> F((B -> A) ⊙ B) -> F(A)

  /** Adjunction between ⊙[*, X] and X |-> * */
  def isoClosedAdjunction[A, X, B]: (⊙[A, X] -> B) <=> (A -> (X |-> B)) = Iso.unsafe(curry, uncurry)

  def closedAdjunction[X](using
    c: SubcatHasId[->, X],
    exo: Exo[->, ->, |->[X, *]]
  ): Exoadjunction[->, ->, ⊙[*, X], |->[X, *]] =
    new Exoadjunction[->, ->, ⊙[*, X], |->[X, *]] {
      val subL: Subcat.Aux[->, TC] = C
      val subR: Subcat.Aux[->, TC] = C
      def left: Exo[->, ->, ⊙[*, X]] = Exo.unsafe[->, ->, ⊙[*, X]]([a, b] => (ab: a -> b) => bifunctor.leftMap(ab))
      def right: Exo[->, ->, |->[X, *]] = exo
      def iso[A, B]: (A ⊙ X) -> B <=> (A -> (X |-> B)) = isoClosedAdjunction
    }
}

object Ccc {
  type Aux[->[_,_], P[_,_], ->#[_], PI, E[_,_]] = Ccc[->, P] {
    type |->[A, B] = E[A, B]
    type TC[x] = ->#[x]
    type Id = PI
  }
  type Aux1[->[_, _], ->#[_], P[_, _], E[_, _]] =
    Ccc[->, P] {type |->[A, B] = E[A, B]; type TC[x] = ->#[x]}

  type Homoiconic[->[_,_], P[_,_]] = Ccc[->, P] { type |->[a,b] = ->[a,b]; type ⊙[a,b] = P[a,b] }

  trait Proto[->[_,_], P[_,_], ->#[_], PI, E[_,_]] extends Ccc[->, P] with Cartesian.Proto[->, P, ->#, PI] {
    type |->[A, B] = E[A, B]
  }

}
