package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

trait Monoidal[->[_,_], ⊙[_,_]] extends Associative[->, ⊙]:
  type Id

  def idl  [A: TC]: ⊙[Id, A] -> A
  def coidl[A: TC]: A -> ⊙[Id, A]
  def idr  [A: TC]: ⊙[A, Id] -> A
  def coidr[A: TC]: A -> ⊙[A, Id]

  private type <->[a, b] = Iso[->, a, b]
  def isoUnitorL[A: TC]: ⊙[Id, A] <-> A = Iso.unsafe(idl[A], coidl[A])(using C)
  def isoUnitorR[A: TC]: ⊙[A, Id] <-> A = Iso.unsafe(idr[A], coidr[A])(using C)

object Monoidal extends MonoidalInstances:
  type Aux [->[_,_], ⊙[_,_], TC0[_], I] = Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }
  type AuxI[->[_,_], ⊙[_,_], I]         = Monoidal[->, ⊙] { type Id = I }
  type AuxT[->[_,_], ⊙[_,_], TC0[_]]    = Monoidal[->, ⊙] { type TC[a] = TC0[a] }
  def apply[->[_,_], ⊙[_,_]](using M: Monoidal[->, ⊙]): Monoidal[->, ⊙] = M

  trait Proto[->[_,_], ⊙[_,_], TC0[_], I] extends Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }

end Monoidal

trait MonoidalK[->[_,_], ⊙[_,_]] extends AssociativeK[->, ⊙]:
  type Id[_]

  def idl  [A[_]: TC]: ∀[[a] =>> ⊙[Id[a], A[a]] -> A[a]]
  def coidl[A[_]: TC]: ∀[[a] =>> A[a] -> ⊙[Id[a], A[a]]]
  def idr  [A[_]: TC]: ∀[[a] =>> ⊙[A[a], Id[a]] -> A[a]]
  def coidr[A[_]: TC]: ∀[[a] =>> A[a] -> ⊙[A[a], Id[a]]]

  private type <->[a[_], b[_]] = IsoK[->, a, b]
  def isoUnitorL[A[_]: TC]: ([a] =>> ⊙[Id[a], A[a]]) <-> A = IsoK.unsafe[->, [a] =>> ⊙[Id[a], A[a]], A](idl[A], coidl[A])(using C.semicat)
  def isoUnitorR[A[_]: TC]: ([a] =>> ⊙[A[a], Id[a]]) <-> A = IsoK.unsafe[->, [a] =>> ⊙[A[a], Id[a]], A](idr[A], coidr[A])(using C.semicat)

object MonoidalK:
  type Aux [->[_,_], ⊙[_,_], TC0[_[_]], I[_]] = MonoidalK[->, ⊙] { type TC[a[_]] = TC0[a]; type Id[a] = I[a] }
  type AuxI[->[_,_], ⊙[_,_], I[_]]            = MonoidalK[->, ⊙] { type Id[a] = I[a] }
  type AuxT[->[_,_], ⊙[_,_], TC0[_[_]]]       = MonoidalK[->, ⊙] { type TC[a[_]] = TC0[a] }
  def apply[->[_,_], ⊙[_,_]](using M: MonoidalK[->, ⊙]): MonoidalK[->, ⊙] = M

  trait Proto[->[_,_], ⊙[_,_], TC0[_[_]], I[_]] extends MonoidalK[->, ⊙] { type TC[a[_]] = TC0[a]; type Id[a] = I[a] }

end MonoidalK

trait MonoidalK2[->[_,_], ⊙[_,_]] extends AssociativeK2[->, ⊙]:
  type Id[_,_]

  def idl  [A[_,_]: TC]: ∀∀[[a, b] =>> ⊙[Id[a, b], A[a, b]] -> A[a, b]]
  def coidl[A[_,_]: TC]: ∀∀[[a, b] =>> A[a, b] -> ⊙[Id[a, b], A[a, b]]]
  def idr  [A[_,_]: TC]: ∀∀[[a, b] =>> ⊙[A[a, b], Id[a, b]] -> A[a, b]]
  def coidr[A[_,_]: TC]: ∀∀[[a, b] =>> A[a, b] -> ⊙[A[a, b], Id[a, b]]]

  private type <->[a[_,_], b[_,_]] = IsoK2[->, a, b]
  def isoUnitorL[A[_,_]: TC]: ([a, b] =>> ⊙[Id[a, b], A[a, b]]) <-> A = IsoK2.unsafe[->, [a, b] =>> ⊙[Id[a, b], A[a, b]], A](idl[A], coidl[A])(using C.semicat)
  def isoUnitorR[A[_,_]: TC]: ([a, b] =>> ⊙[A[a, b], Id[a, b]]) <-> A = IsoK2.unsafe[->, [a, b] =>> ⊙[A[a, b], Id[a, b]], A](idr[A], coidr[A])(using C.semicat)

object MonoidalK2:
  type Aux [->[_,_], ⊙[_,_], TC0[_[_,_]], I[_,_]] = MonoidalK2[->, ⊙] { type TC[a[_,_]] = TC0[a]; type Id[a, b] = I[a, b] }
  type AuxI[->[_,_], ⊙[_,_], I[_,_]]              = MonoidalK2[->, ⊙] { type Id[a, b] = I[a, b] }
  type AuxT[->[_,_], ⊙[_,_], TC0[_[_,_]]]         = MonoidalK2[->, ⊙] { type TC[a[_,_]] = TC0[a] }
  def apply[->[_,_], ⊙[_,_]](using M: MonoidalK2[->, ⊙]): MonoidalK2[->, ⊙] = M

  trait Proto[->[_,_], ⊙[_,_], TC0[_[_,_]], I[_,_]] extends MonoidalK2[->, ⊙] { type TC[a[_,_]] = TC0[a]; type Id[a, b] = I[a, b] }

end MonoidalK2

trait MonoidalH[->[_,_], ⊙[_,_]] extends AssociativeH[->, ⊙]:
  type Id[_[_]]
  def idl  [A[_[_]] : TC]: ∀~[[a[_]] =>> ⊙[Id[a], A[a]] -> A[a]]
  def coidl[A[_[_]] : TC]: ∀~[[a[_]] =>> A[a] -> ⊙[Id[a], A[a]]]
  def idr  [A[_[_]] : TC]: ∀~[[a[_]] =>> ⊙[A[a], Id[a]] -> A[a]]
  def coidr[A[_[_]] : TC]: ∀~[[a[_]] =>> A[a] -> ⊙[A[a], Id[a]]]

  private type <->[a[_[_]], b[_[_]]] = IsoH[->, a, b]
  def isoUnitorL[A[_[_]] : TC]: ([a[_]] =>> ⊙[Id[a], A[a]]) <-> A = IsoH.unsafe[->, [a[_]] =>> ⊙[Id[a], A[a]], A](idl[A], coidl[A])(using C.semicat)
  def isoUnitorR[A[_[_]] : TC]: ([a[_]] =>> ⊙[A[a], Id[a]]) <-> A = IsoH.unsafe[->, [a[_]] =>> ⊙[A[a], Id[a]], A](idr[A], coidr[A])(using C.semicat)

object MonoidalH:
  type Aux [->[_,_], ⊙[_,_], TC0[_[_[_]]], I[_[_]]] = MonoidalH[->, ⊙] {type TC[a[_[_]]] = TC0[a]; type Id[a[_]] = I[a]}
  type AuxI[->[_,_], ⊙[_,_], I[_[_]]] = MonoidalH[->, ⊙] {type Id[a[_]] = I[a]}
  type AuxT[->[_,_], ⊙[_,_], TC0[_[_[_]]]] = MonoidalH[->, ⊙] {type TC[a[_[_]]] = TC0[a]}

  def apply[->[_,_], ⊙[_,_]](using M: MonoidalH[->, ⊙]): MonoidalH[->, ⊙] = M

  trait Proto[->[_,_], ⊙[_,_], TC0[_[_[_]]], I[_[_]]]
    extends MonoidalH[->, ⊙] { type TC[a[_[_]]] = TC0[a]; type Id[a[_]] = I[a] }

end MonoidalH

trait MonoidalInstances {
  // TODO: de facut
}