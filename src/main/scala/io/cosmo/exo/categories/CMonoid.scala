package io.cosmo.exo.categories

import io.cosmo.exo._

trait CMonoid[->[_,_], ⊙[_,_], A] extends CSemigroup[->, ⊙, A]:
  type I
  def C: Monoidal.AuxI[->, ⊙, I]
  def id: I -> A

object CMonoid:
  type Aux[->[_,_], ⊙[_,_], A, I0] = CMonoid[->, ⊙, A] {type I = I0}

  def unsafe[->[_,_], ⊙[_,_], A, I0](fe: I0 -> A, f: (A ⊙ A) -> A)(using m: Monoidal.AuxI[->, ⊙, I0]
  ): CMonoid.Aux[->, ⊙, A, I0] =
    new CMonoid[->, ⊙, A] {type I = I0; val C = m; val id = fe; val op = f}

  def fromSemigroup[->[_,_], ⊙[_,_], A, I0](fe: I0 -> A, s: CSemigroup[->, ⊙, A])(using m: Monoidal.AuxI[->, ⊙, I0]
  ): CMonoid.Aux[->, ⊙, A, I0] = unsafe(fe, s.op)

trait CMonoidK[->[_,_], ⊙[_,_], F[_]] extends CSemigroupK[->, ⊙, F]:
  type I[_]
  def C: MonoidalK.AuxI[->, ⊙, I]
  def id: ∀[[a] =>> I[a] -> F[a]]
  def idFn[A]: I[A] -> F[A] = id[A]

object CMonoidK:
  type Aux[->[_,_], ⊙[_,_], F[_], I0[_]] = CMonoidK[->, ⊙, F] {type I[a] = I0[a]}

  def unsafe[->[_,_], ⊙[_,_], F[_], I0[_]](fe: ∀[[a] =>> I0[a] -> F[a]], f: ∀[[a] =>> (F[a] ⊙ F[a]) -> F[a]])(using m: MonoidalK.AuxI[->, ⊙, I0]
  ): CMonoidK.Aux[->, ⊙, F, I0] =
    new CMonoidK[->, ⊙, F] {type I[a] = I0[a]; val C = m; val id = fe; val op = f}

  def fromSemigroupK[->[_,_], ⊙[_,_], F[_], I0[_]](fe: ∀[[a] =>> I0[a] -> F[a]], s: CSemigroupK[->, ⊙, F])(using m: MonoidalK.AuxI[->, ⊙, I0]
  ): CMonoidK.Aux[->, ⊙, F, I0] = unsafe(fe, s.op)

  trait Proto[->[_,_], ⊙[_,_], F[_], I0[_]] extends CSemigroupK.Proto[->, ⊙, F] with CMonoidK[->, ⊙, F]:
    type I[a] = I0[a]
    protected def idK[A]: I[A] -> F[A]
    def id: ∀[[a] =>> I[a] -> F[a]] = ∀[[a] =>> I[a] -> F[a]](idK)

trait CMonoidK2[->[_,_], ⊙[_,_], F[_,_]] extends CSemigroupK2[->, ⊙, F]:
  type I[_,_]
  def C: MonoidalK2.AuxI[->, ⊙, I]
  def id: ∀∀[[a, b] =>> I[a, b] -> F[a, b]]
  def idFn[A, B]: I[A, B] -> F[A, B] = id[A, B]

object CMonoidK2:
  type Aux[->[_,_], ⊙[_,_], F[_,_], I0[_,_]] = CMonoidK2[->, ⊙, F] { type I[a, b] = I0[a, b] }

  def unsafe[->[_,_], ⊙[_,_], F[_,_], I0[_,_]](
    fe: ∀∀[[a, b] =>> I0[a, b] -> F[a, b]],
    f:  ∀∀[[a, b] =>> (F[a, b] ⊙ F[a, b]) -> F[a, b]]
  )(using m: MonoidalK2.AuxI[->, ⊙, I0]): CMonoidK2.Aux[->, ⊙, F, I0] =
    new CMonoidK2[->, ⊙, F] {type I[a, b] = I0[a, b]; val C = m; val id = fe; val op = f}

  def fromSemigroupK2[->[_,_], ⊙[_,_], F[_,_], I0[_,_]](
    fe: ∀∀[[a, b] =>> I0[a, b] -> F[a, b]],
    s: CSemigroupK2[->, ⊙, F]
  )(using m: MonoidalK2.AuxI[->, ⊙, I0]): CMonoidK2.Aux[->, ⊙, F, I0] = unsafe(fe, s.op)

  trait Proto[->[_,_], ⊙[_,_], F[_,_], I0[_,_]] extends CSemigroupK2.Proto[->, ⊙, F] with CMonoidK2[->, ⊙, F]:
    type I[a, b] = I0[a, b]
    protected def idK2[A, B]: I[A, B] -> F[A, B]
    def id: ∀∀[[a, b] =>> I[a, b] -> F[a, b]] = ∀∀[[a, b] =>> I[a, b] -> F[a, b]](idK2)

trait CMonoidH[->[_,_], ⊙[_,_], F[_[_]]] extends CSemigroupH[->, ⊙, F]:
  type I[_[_]]
  def C: MonoidalH.AuxI[->, ⊙, I]
  def id: ∀~[[a[_]] =>> I[a] -> F[a]]
  def idFn[A[_]]: I[A] -> F[A] = id[A]

object CMonoidH:
  type Aux[->[_,_], ⊙[_,_], F[_[_]], I0[_[_]]] = CMonoidH[->, ⊙, F] { type I[a[_]] = I0[a] }

  def unsafe[->[_,_], ⊙[_,_], F[_[_]], I0[_[_]]](
    fe: ∀~[[a[_]] =>> I0[a] -> F[a]],
    f:  ∀~[[a[_]] =>> (F[a] ⊙ F[a]) -> F[a]]
  )(using m: MonoidalH.AuxI[->, ⊙, I0]): CMonoidH.Aux[->, ⊙, F, I0] =
    new CMonoidH[->, ⊙, F] {type I[a[_]] = I0[a]; val C = m; val id = fe; val op = f}

  def fromSemigroupH[->[_,_], ⊙[_,_], F[_[_]], I0[_[_]]](
    fe: ∀~[[a[_]] =>> I0[a] -> F[a]],
    s: CSemigroupH[->, ⊙, F]
  )(using m: MonoidalH.AuxI[->, ⊙, I0]): CMonoidH.Aux[->, ⊙, F, I0] = unsafe(fe, s.op)

  trait Proto[->[_,_], ⊙[_,_], F[_[_]], I0[_[_]]] extends CSemigroupH.Proto[->, ⊙, F] with CMonoidH[->, ⊙, F]:
    type I[a[_]] = I0[a]
    protected def idH[A[_]]: I[A] -> F[A]
    def id: ∀~[[a[_]] =>> I[a] -> F[a]] = ∀~[[a[_]] =>> I[a] -> F[a]](idH)
