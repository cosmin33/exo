package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

trait Symmetric[->[_,_], ⊙[_,_]] extends Braided[->, ⊙]:
  def swap[A: TC, B: TC]: ⊙[A, B] -> ⊙[B, A] = braid

  private type <->[a, b] = Iso[->, a, b]
  def isoSymmetric[A: TC, B: TC]: ⊙[A, B] <-> ⊙[B, A] = Iso.unsafe(swap[A, B], swap[B, A])(using C)

object Symmetric:
  def apply[->[_,_], ⊙[_,_]](using ev: Symmetric[->, ⊙]): Symmetric[->, ⊙] = ev
  type Aux[->[_,_], ⊙[_,_], TC0[_]] = Symmetric[->, ⊙] {type TC[a] = TC0[a]}
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, Trivial]
  trait Proto[->[_,_], ⊙[_,_], TC0[_]] extends Symmetric[->, ⊙] { type TC[a] = TC0[a] }

end Symmetric

trait SymmetricK[->[_,_], ⊙[_,_]] extends BraidedK[->, ⊙]:
  def swap[A[_]: TC, B[_]: TC]: ∀[[a] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]] = braid

  private type <->[a[_], b[_]] = IsoK[->, a, b]
  def isoSymmetric[A[_]: TC, B[_]: TC]: ([a] =>> ⊙[A[a], B[a]]) <-> ([a] =>> ⊙[B[a], A[a]]) =
    IsoK.unsafe[->, [a] =>> ⊙[A[a], B[a]], [a] =>> ⊙[B[a], A[a]]](swap[A, B], swap[B, A])(using C.lower)

object SymmetricK:
  def apply[->[_,_], ⊙[_,_]](using ev: SymmetricK[->, ⊙]): SymmetricK[->, ⊙] = ev
  type Aux[->[_,_], ⊙[_,_], TC0[_[_]]] = SymmetricK[->, ⊙] {type TC[a[_]] = TC0[a]}
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, TrivialK]
  trait Proto[->[_,_], ⊙[_,_], TC0[_[_]]] extends SymmetricK[->, ⊙] { type TC[a[_]] = TC0[a] }

end SymmetricK

trait SymmetricK2[->[_,_], ⊙[_,_]] extends BraidedK2[->, ⊙]:
  def swap[A[_,_]: TC, B[_,_]: TC]: ∀∀[[a, b] =>> ⊙[A[a, b], B[a, b]] -> ⊙[B[a, b], A[a, b]]] = braid

  private type <->[a[_,_], b[_,_]] = IsoK2[->, a, b]
  def isoSymmetric[A[_,_]: TC, B[_,_]: TC]: ([a, b] =>> ⊙[A[a, b], B[a, b]]) <-> ([a, b] =>> ⊙[B[a, b], A[a, b]]) =
    IsoK2.unsafe[->, [a, b] =>> ⊙[A[a, b], B[a, b]], [a, b] =>> ⊙[B[a, b], A[a, b]]](swap[A, B], swap[B, A])(using C.lower)

object SymmetricK2:
  def apply[->[_,_], ⊙[_,_]](using ev: SymmetricK2[->, ⊙]): SymmetricK2[->, ⊙] = ev
  type Aux[->[_,_], ⊙[_,_], TC0[_[_,_]]] = SymmetricK2[->, ⊙] {type TC[a[_,_]] = TC0[a]}
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, TrivialK2]
  trait Proto[->[_,_], ⊙[_,_], TC0[_[_,_]]] extends SymmetricK2[->, ⊙] { type TC[a[_,_]] = TC0[a] }

end SymmetricK2

trait SymmetricH[->[_,_], ⊙[_,_]] extends BraidedH[->, ⊙]:
  def swap[A[_[_]]: TC, B[_[_]]: TC]: ∀~[[a[_]] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]] = braid

  private type <->[a[_[_]], b[_[_]]] = IsoH[->, a, b]
  def isoSymmetric[A[_[_]]: TC, B[_[_]]: TC]: ([a[_]] =>> ⊙[A[a], B[a]]) <-> ([a[_]] =>> ⊙[B[a], A[a]]) =
    IsoH.unsafe[->, [a[_]] =>> ⊙[A[a], B[a]], [a[_]] =>> ⊙[B[a], A[a]]](swap[A, B], swap[B, A])(using C.lower)

object SymmetricH:
  def apply[->[_,_], ⊙[_,_]](using ev: SymmetricH[->, ⊙]): SymmetricH[->, ⊙] = ev
  type Aux[->[_,_], ⊙[_,_], TC0[_[_[_]]]] = SymmetricH[->, ⊙] {type TC[a[_[_]]] = TC0[a]}
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, TrivialH]
  trait Proto[->[_,_], ⊙[_,_], TC0[_[_[_]]]] extends SymmetricH[->, ⊙] { type TC[a[_[_]]] = TC0[a] }

end SymmetricH
