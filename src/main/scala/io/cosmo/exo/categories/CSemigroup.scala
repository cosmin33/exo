package io.cosmo.exo.categories

import io.cosmo.exo._

trait CSemigroup[->[_,_], ⊙[_,_], A]:
  def C: Associative[->, ⊙]
  def op: (A ⊙ A) -> A

object CSemigroup:
  def unsafe[->[_,_], ⊙[_,_], A](f: (A ⊙ A) -> A)(using m: Associative[->, ⊙]): CSemigroup[->, ⊙, A] =
    new CSemigroup[->, ⊙, A] {val C = m; val op = f}

trait CSemigroupK[->[_,_], ⊙[_,_], F[_]]:
  def C: AssociativeK[->, ⊙]
  def op: ∀[[a] =>> (F[a] ⊙ F[a]) -> F[a]]
  def opFn[A]: (F[A] ⊙ F[A]) -> F[A] = op[A]

object CSemigroupK:
  def unsafe[->[_,_], ⊙[_,_], F[_]](f: ∀[[a] =>> (F[a] ⊙ F[a]) -> F[a]])(using m: AssociativeK[->, ⊙]): CSemigroupK[->, ⊙, F] =
    new CSemigroupK[->, ⊙, F] {val C = m; val op = f}
  trait Proto[->[_,_], ⊙[_,_], F[_]] extends CSemigroupK[->, ⊙, F]:
    protected def opK[A]: (F[A] ⊙ F[A]) -> F[A]
    def op: ∀[[a] =>> (F[a] ⊙ F[a]) -> F[a]] = ∀[[a] =>> (F[a] ⊙ F[a]) -> F[a]](opK)

trait CSemigroupK2[->[_,_], ⊙[_,_], F[_,_]]:
  def C: AssociativeK2[->, ⊙]
  def op: ∀∀[[a, b] =>> (F[a, b] ⊙ F[a, b]) -> F[a, b]]
  def opFn[A, B]: (F[A, B] ⊙ F[A, B]) -> F[A, B] = op[A, B]

object CSemigroupK2:
  def unsafe[->[_,_], ⊙[_,_], F[_,_]](f: ∀∀[[a, b] =>> (F[a, b] ⊙ F[a, b]) -> F[a, b]])(using m: AssociativeK2[->, ⊙]): CSemigroupK2[->, ⊙, F] =
    new CSemigroupK2[->, ⊙, F] { val C = m; val op = f }
  trait Proto[->[_,_], ⊙[_,_], F[_,_]] extends CSemigroupK2[->, ⊙, F]:
    protected def opK2[A, B]: (F[A, B] ⊙ F[A, B]) -> F[A, B]
    def op: ∀∀[[a, b] =>> (F[a, b] ⊙ F[a, b]) -> F[a, b]] = ∀∀[[a, b] =>> (F[a, b] ⊙ F[a, b]) -> F[a, b]](opK2)

trait CSemigroupH[->[_,_], ⊙[_,_], F[_[_]]]:
  def C: AssociativeH[->, ⊙]
  def op: ∀~[[a[_]] =>> (F[a] ⊙ F[a]) -> F[a]]
  def opFn[A[_]]: (F[A] ⊙ F[A]) -> F[A] = op[A]

object CSemigroupH:
  def unsafe[->[_,_], ⊙[_,_], F[_[_]]](f: ∀~[[a[_]] =>> (F[a] ⊙ F[a]) -> F[a]])(using m: AssociativeH[->, ⊙]): CSemigroupH[->, ⊙, F] =
    new CSemigroupH[->, ⊙, F] { val C = m; val op = f }
  trait Proto[->[_,_], ⊙[_,_], F[_[_]]] extends CSemigroupH[->, ⊙, F]:
    protected def opH[A[_]]: (F[A] ⊙ F[A]) -> F[A]
    def op: ∀~[[a[_]] =>> (F[a] ⊙ F[a]) -> F[a]] = ∀~[[a[_]] =>> (F[a] ⊙ F[a]) -> F[a]](opH)
