package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

trait Braided[->[_,_], ⊙[_,_]] extends Associative[->, ⊙]:
  def braid[A: TC, B: TC]: ⊙[A, B] -> ⊙[B, A]

object Braided:
  type Aux[->[_,_], ⊙[_,_], TC0[_]] = Braided[->, ⊙] { type TC[a] = TC0[a] }
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, Trivial]
  trait Proto[->[_,_], ⊙[_,_], TC0[_]] extends Braided[->, ⊙] { type TC[a] = TC0[a] }
  
end Braided

trait BraidedK[->[_,_], ⊙[_,_]] extends AssociativeK[->, ⊙]:
  def braid[A[_]: TC, B[_]: TC]: ∀[[a] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]]

object BraidedK:
  type Aux[->[_,_], ⊙[_,_], TC0[_[_]]] = BraidedK[->, ⊙] { type TC[a[_]] = TC0[a] }
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, TrivialK]
  trait Proto[->[_,_], ⊙[_,_], TC0[_[_]]] extends BraidedK[->, ⊙] { type TC[a[_]] = TC0[a] }

end BraidedK

trait BraidedK2[->[_,_], ⊙[_,_]] extends AssociativeK2[->, ⊙]:
  def braid[A[_,_]: TC, B[_,_]: TC]: ∀∀[[a, b] =>> ⊙[A[a, b], B[a, b]] -> ⊙[B[a, b], A[a, b]]]

object BraidedK2:
  type Aux[->[_,_], ⊙[_,_], TC0[_[_,_]]] = BraidedK2[->, ⊙] { type TC[a[_,_]] = TC0[a] }
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, TrivialK2]
  trait Proto[->[_,_], ⊙[_,_], TC0[_[_,_]]] extends BraidedK2[->, ⊙] { type TC[a[_,_]] = TC0[a] }

end BraidedK2

trait BraidedH[->[_,_], ⊙[_,_]] extends AssociativeH[->, ⊙]:
  def braid[A[_[_]]: TC, B[_[_]]: TC]: ∀~[[a[_]] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]]

object BraidedH:
  type Aux[->[_,_], ⊙[_,_], TC0[_[_[_]]]] = BraidedH[->, ⊙] { type TC[a[_[_]]] = TC0[a] }
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, TrivialH]
  trait Proto[->[_,_], ⊙[_,_], TC0[_[_[_]]]] extends BraidedH[->, ⊙] { type TC[a[_[_]]] = TC0[a] }

end BraidedH
