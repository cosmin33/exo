package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.categories.instances.MonoidalInstances

trait Monoidal[->[_, _], ⊙[_, _]] extends Associative[->, ⊙] {
  type Id

  def idl  [A]: ⊙[Id, A] -> A
  def coidl[A]: A -> ⊙[Id, A]

  def idr  [A]: ⊙[A, Id] -> A
  def coidr[A]: A -> ⊙[A, Id]

  private type <->[a, b] = Iso[->, a, b]
  def isoIdL[A]: ⊙[Id, A] <-> A = Iso.unsafe(idl[A], coidl[A])(C)
  def isoIdR[A]: ⊙[A, Id] <-> A = Iso.unsafe(idr[A], coidr[A])(C)
}

object Monoidal extends MonoidalInstances {
  def apply[->[_, _], ⊙[_, _]](implicit M: Monoidal[->, ⊙]): Monoidal[->, ⊙] = M
  type Aux  [->[_, _], ⊙[_, _], TC0[_], I] = Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }
  type AuxI [->[_, _], ⊙[_, _], I]         = Monoidal[->, ⊙] { type Id = I }
  type AuxTC[->[_, _], ⊙[_, _], TC0[_]]    = Monoidal[->, ⊙] { type TC[a] = TC0[a] }
  type AuxT [->[_, _], ⊙[_, _]] = AuxTC[->, ⊙, Trivial.T1]

  /** Prototype for easily creating a Monoidal if you already have an Associative */
  abstract class ProtoAssociative[->[_, _], ⊙[_, _], TC0[_]](A: Associative.Aux[->, ⊙, TC0]) extends Monoidal[->, ⊙] {
    type TC[a] = TC0[a]
    val C: Subcat.Aux[->, TC0] = A.C
    val bifunctor = A.bifunctor
    def associate  [X, Y, Z] = A.associate
    def diassociate[X, Y, Z] = A.diassociate
  }

}
