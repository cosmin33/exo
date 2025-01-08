package io.cosmo.exo.categories

import io.cosmo.exo._

trait Concrete[->[_,_]] extends Subcat[->]:
  def concretize[A, B](f: A -> B): (A, TC[A]) => (B, TC[B])
  def toFunction[A: TC, B](f: A -> B): A => B = concretize(f)(_, summon)._1
object Concrete:
  type Aux[->[_,_], C0[_]] = Concrete[->] { type TC[ᵒ] = C0[ᵒ] }
  type AuxT[->[_,_]] = Aux[->, Trivial]

trait ConcreteK[->[_,_]] extends SubcatK[->]:
  def concretize[F[_], G[_]](f: ∀[[a] =>> F[a] -> G[a]]): ∀[[a] =>> (F[a], TC[F]) => (G[a], TC[G])]
  def toFunction[F[_]: TC, G[_]](f: ∀[[a] =>> F[a] -> G[a]]): F ~> G =
    ∀.of[[a] =>> F[a] => G[a]].fromH([a] => () => (fa: F[a]) => concretize(f)[a](fa, summon)._1)
object ConcreteK:
  type Aux[->[_,_], C0[_[_]]] = ConcreteK[->] { type TC[a[_]] = C0[a] }
  type AuxT[->[_,_]] = Aux[->, TrivialK]

trait ConcreteK2[->[_,_]] extends SubcatK2[->]:
  def concretize[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]]): ∀∀[[a, b] =>> (F[a, b], TC[F]) => (G[a, b], TC[G])]
  def toFunction[F[_,_]: TC, G[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]]): F ~~> G =
    ∀∀.of[[a, b] =>> F[a, b] => G[a, b]].fromH([a, b] => () => (fa: F[a, b]) => concretize(f)[a, b](fa, summon)._1)
object ConcreteK2:
  type Aux[->[_,_], C0[_[_,_]]] = ConcreteK2[->] { type TC[a[_,_]] = C0[a] }
  type AuxT[->[_,_]] = Aux[->, TrivialK2]

trait ConcreteH[->[_,_]] extends SubcatH[->]:
  def concretize[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]]): ∀~[[a[_]] =>> (F[a], TC[F]) => (G[a], TC[G])]
  def toFunction[F[_[_]]: TC, G[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]]): F ≈> G =
    ∀~.of[[a[_]] =>> F[a] => G[a]].fromH([a[_]] => () => (fa: F[a]) => concretize(f)[a](fa, summon)._1)
object ConcreteH:
  type Aux[->[_,_], C0[_[_[_]]]] = ConcreteH[->] { type TC[a[_[_]]] = C0[a] }
  type AuxT[->[_,_]] = Aux[->, TrivialH]
