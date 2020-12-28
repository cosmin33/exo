package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.categories.instances.MonoidalInstances

trait Monoidal[->[_, _], ⊙[_, _]] extends Associative[->, ⊙] {
  type Id

  def idl  [A: TC]: ⊙[Id, A] -> A
  def coidl[A: TC]: A -> ⊙[Id, A]
  def idr  [A: TC]: ⊙[A, Id] -> A
  def coidr[A: TC]: A -> ⊙[A, Id]

  private type <->[a, b] = Iso[->, a, b]
  def isoUnitorL[A: TC]: ⊙[Id, A] <-> A = Iso.unsafe(idl[A], coidl[A])(C)
  def isoUnitorR[A: TC]: ⊙[A, Id] <-> A = Iso.unsafe(idr[A], coidr[A])(C)
}

object Monoidal extends MonoidalInstances {
  def apply[->[_, _], ⊙[_, _]](implicit M: Monoidal[->, ⊙]): Monoidal[->, ⊙] = M
  type Aux  [->[_, _], ⊙[_, _], TC0[_], I] = Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }
  type AuxI [->[_, _], ⊙[_, _], I]         = Monoidal[->, ⊙] { type Id = I }
  type AuxTC[->[_, _], ⊙[_, _], TC0[_]]    = Monoidal[->, ⊙] { type TC[a] = TC0[a] }
  type AuxT [->[_, _], ⊙[_, _]] = AuxTC[->, ⊙, Trivial.T1]

  /** Prototype for easily creating a Monoidal if you already have an Associative */
  abstract class ProtoFromAssociative[->[_, _], ⊙[_, _], TC0[_]](A: Associative.Aux[->, ⊙, TC0]) extends Monoidal[->, ⊙] {
    type TC[a] = TC0[a]
    val C: Subcat.Aux[->, TC0] = A.C
    val bifunctor = A.bifunctor
    def associate  [X, Y, Z] = A.associate
    def diassociate[X, Y, Z] = A.diassociate
  }

}
