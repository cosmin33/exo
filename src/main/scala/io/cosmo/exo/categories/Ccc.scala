package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.syntax.*

trait Ccc[->[_,_], ⊙[_,_], |->[_,_]] extends Cartesian[->, ⊙]:
  self =>
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
    new Exoadjunction[->, ->, ⊙[*, X], |->[X, *]]:
      val subL: Subcat.Aux[->, TC] = C
      val subR: Subcat.Aux[->, TC] = C
      def left: Exo[->, ->, ⊙[*, X]] = Exo.unsafe[->, ->, ⊙[*, X]]([a, b] => (ab: a -> b) => bifunctor.leftMap(ab))
      def right: Exo[->, ->, |->[X, *]] = exo
      def iso[A, B]: (A ⊙ X) -> B <=> (A -> (X |-> B)) = isoClosedAdjunction

object Ccc:
  type Aux[->[_,_], P[_,_], E[_,_], ->#[_], I] = Ccc[->, P, E] { type TC[x] = ->#[x]; type Id = I }
  type Aux1[->[_,_], ->#[_], P[_,_], E[_,_]] = Ccc[->, P, E] { type TC[x] = ->#[x] }
  
  trait Proto[->[_,_], P[_,_], ->#[_], PI, |->[_,_]] extends Ccc[->, P, |->] with Cartesian.Proto[->, P, ->#, PI]
end Ccc

trait CccK[->[_,_], ⊙[_,_], |->[_,_]] extends CartesianK[->, ⊙]:
  self =>
  def curry  [F[_], G[_], H[_]](f: ∀[[a] =>> (F[a] ⊙ G[a]) -> H[a]]): ∀[[a] =>> F[a] -> (G[a] |-> H[a])]
  def uncurry[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> (G[a] |-> H[a])]): ∀[[a] =>> (F[a] ⊙ G[a]) -> H[a]]

object CccK:
  type Aux[->[_,_], P[_,_], E[_,_], ->#[_[_]], I[_]] = CccK[->, P, E] { type TC[A[_]] = ->#[A]; type Id[a] = I[a] }
  def apply[->[_,_], ⊙[_,_], |->[_,_]](using ev: CccK[->, ⊙, |->]): CccK[->, ⊙, |->] = ev
end CccK

trait CccK2[->[_,_], ⊙[_,_], |->[_,_]] extends CartesianK2[->, ⊙]:
  self =>
  def curry  [F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> (F[a, b] ⊙ G[a, b]) -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> (G[a, b] |-> H[a, b])]
  def uncurry[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> (G[a, b] |-> H[a, b])]): ∀∀[[a, b] =>> (F[a, b] ⊙ G[a, b]) -> H[a, b]]

object CccK2:
  type Aux[->[_,_], P[_,_], E[_,_], ->#[_[_,_]], I[_,_]] = CccK2[->, P, E] { type TC[A[_,_]] = ->#[A]; type Id[a,b] = I[a,b] }
  def apply[->[_,_], ⊙[_,_], |->[_,_]](using ev: CccK2[->, ⊙, |->]): CccK2[->, ⊙, |->] = ev
end CccK2

trait CccH[->[_,_], ⊙[_,_], |->[_,_]] extends CartesianH[->, ⊙]:
  self =>
  def curry  [F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> (F[a] ⊙ G[a]) -> H[a]]): ∀~[[a[_]] =>> F[a] -> (G[a] |-> H[a])]
  def uncurry[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> (G[a] |-> H[a])]): ∀~[[a[_]] =>> (F[a] ⊙ G[a]) -> H[a]]

object CccH:
  type Aux[->[_,_], P[_,_], E[_,_], ->#[_[_[_]]], I[a[_]]] = CccH[->, P, E] { type TC[A[_[_]]] = ->#[A]; type Id[a[_]] = I[a] }
  def apply[->[_,_], ⊙[_,_], |->[_,_]](using ev: CccH[->, ⊙, |->]): CccH[->, ⊙, |->] = ev
end CccH

