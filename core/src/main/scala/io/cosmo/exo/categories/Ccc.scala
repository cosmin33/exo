package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.functors._

trait Ccc[->[_,_]] extends Subcat[->] { self =>
  type |->[_,_] // Hom objects representation
  type ⊙[_,_] // product
  type Id
  def cartesian: Cartesian.Aux[->, ⊙, TC, Id]

  def curry  [A, B, C](f: (A ⊙ B) -> C): A -> (B |-> C)
  def uncurry[A, B, C](f: A -> (B |-> C)): (A ⊙ B) -> C

  def rcurry  [A: TC, B: TC, C: TC](f: (A ⊙ B) -> C): B -> (A |-> C) = curry(compose(f, cartesian.swap))
  def runcurry[A: TC, B: TC, C: TC](f: B -> (A |-> C)): (A ⊙ B) -> C = compose(uncurry(f), cartesian.swap)

  def apply  [A, B](using t: TC[A |-> B]): ⊙[A |-> B, A] -> B = uncurry(id[A |-> B])
  def unapply[A, B](using t: TC[A ⊙ B]): A -> (B |-> (A ⊙ B)) = curry(id[A ⊙ B])

  def const[A: TC, B: TC, C](f: B -> C): A -> (B |-> C) = curry(andThen(cartesian.snd[A, B], f))

  def thing[A: TC, B](in: Id -> (A |-> B)): A -> B = andThen(cartesian.coidl[A], uncurry(in))

  /** Iso between `Id -> (A |-> B)` and `A -> B` */
  def isoConstThing[A, B](using ta: TC[A], term: Terminal.Aux[->, TC, Id])
  : (Id -> (A |-> B)) <=> (A -> B) =
    Iso.unsafe(thing(_)(ta), const(_)(using term.TC, ta))

  def precmp [A, B, C](f: A -> B)(using t: TC[C |-> A]): (C |-> A) -> (C |-> B) = curry(andThen(apply[C, A], f))
  def postcmp[A, B, C](f: A -> B)(using t: TC[B |-> C]): (B |-> C) -> (A |-> C) =
    curry(andThen(cartesian.grouped(id[B |-> C], f), apply[B, C]))

  def promap1[A, B, C, D](f: A -> B, g: C -> D)(using tca: TC[C |-> A], tda: TC[D |-> A]): (D |-> A) -> (C |-> B) =
    compose(precmp[A, B, C](f), postcmp[C, D, A](g))
  def promap2[A, B, C, D](f: A -> B, g: C -> D)(using tac: TC[A |-> C], tbc: TC[B |-> C]): (B |-> C) -> (A |-> D) =
    promap1(g, f)

  // Cartesian Closed Functor Laws: (to be deleted once I code the functor)
  // F(B -> A) => F(B) -> F(A)
  // F(B -> A) ⊙ F(B) <=> F((B -> A) ⊙ B) -> F(A)

  /** Adjunction between ⊙[*, B] and B |-> * */
  def isoClosedAdjunction[A, B, C]: (⊙[A, B] -> C) <=> (A -> (B |-> C)) = Iso.unsafe(curry, uncurry)

  def closedAdjunction[X](using
    c: SubcatHasId[->, X],
    t1: ∀[[a] =>> TC[a ⊙ X]],
    t2: ∀[[a] =>> TC[X |-> a]],
    exo: Exo[->, ->, |->[X, *]]
  ): Exoadjunction[->, ->, ⊙[*, X], |->[X, *]] =
    new Exoadjunction[->, ->, ⊙[*, X], |->[X, *]] {
      val subL: Subcat.Aux[->, TC] = self
      val subR: Subcat.Aux[->, TC] = self
      def left: Exo[->, ->, ⊙[*, X]] = Exo.unsafe[->, ->, ⊙[*, X]]([a, b] => (ab: a -> b) => cartesian.bifunctor.leftMap(ab))
      def right: Exo[->, ->, [o] =>> X |-> o] = exo
      override def iso[A, B]: (A ⊙ X) -> B <=> (A -> (X |-> B)) = isoClosedAdjunction
      def unit  [A]: A -> (X |-> (A ⊙ X)) = iso[A,   A ⊙ X].to  (subL.id[A ⊙ X]  (using t1.apply[A]))
      def counit[A]: ((X |-> A) ⊙ X) -> A = iso[X |-> A, A].from(subR.id[X |-> A](using t2.apply[A]))
    }
}

object Ccc {
  type Aux[->[_,_], ->#[_], P[_,_], PI, E[_,_]] = Ccc[->] {
    type |->[A, B] = E[A, B]
    type ⊙[A, B] = P[A, B]
    type TC[x] = ->#[x]
    type Id = PI
  }
  type Aux1[->[_,_], ->#[_], P[_,_], E[_,_]] =
    Ccc[->] {type |->[A, B] = E[A, B]; type ⊙[A, B] = P[A, B]; type TC[x] = ->#[x]}

  type Homoiconic[->[_,_]] = Ccc[->] { type |->[a,b] = ->[a,b] }

  trait Proto[->[_,_], P[_,_], ->#[_], PI, E[_,_]] extends Ccc[->] with Subcat.Proto[->, ->#] {
    override type TC[a] = ->#[a]
    type |->[A, B] = E[A, B]
    type ⊙[A, B] = P[A, B]
    type Id = PI
  }

}
