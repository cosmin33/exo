package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

trait Monoidal[->[_,_], ⊙[_,_]] extends Associative[->, ⊙] {
  type Id

  def idl  [A: TC]: ⊙[Id, A] -> A
  def coidl[A: TC]: A -> ⊙[Id, A]
  def idr  [A: TC]: ⊙[A, Id] -> A
  def coidr[A: TC]: A -> ⊙[A, Id]

  private type <->[a, b] = Iso[->, a, b]
  def isoUnitorL[A: TC]: ⊙[Id, A] <-> A = Iso.unsafe(idl[A], coidl[A])(using C)
  def isoUnitorR[A: TC]: ⊙[A, Id] <-> A = Iso.unsafe(idr[A], coidr[A])(using C)
}

object Monoidal extends MonoidalInstances {
  def apply[->[_,_], ⊙[_,_]](using M: Monoidal[->, ⊙]): Monoidal[->, ⊙] = M
  type Aux  [->[_,_], ⊙[_,_], TC0[_], I] = Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }
  type AuxI [->[_,_], ⊙[_,_], I]         = Monoidal[->, ⊙] { type Id = I }
  type AuxTC[->[_,_], ⊙[_,_], TC0[_]]    = Monoidal[->, ⊙] { type TC[a] = TC0[a] }

  trait Proto[->[_,_], ⊙[_,_], TC0[_], I] extends Monoidal[->, ⊙] { type TC[a] = TC0[a]; type Id = I }
  
  /** Prototype for easily creating a Monoidal if you already have an Associative */
  abstract class ProtoFromAssociative[->[_,_], ⊙[_,_], TC0[_]](A: Associative.Aux[->, ⊙, TC0]) extends Monoidal[->, ⊙] {
    type TC[a] = TC0[a]
    val C: Subcat.Aux[->, TC0] = A.C
    val bifunctor = A.bifunctor
    def associate  [X: TC, Y: TC, Z: TC] = A.associate
    def diassociate[X: TC, Y: TC, Z: TC] = A.diassociate
  }

  extension[->[_,_], ⊙[_,_], I[_]](a: MonoidalK.Aux[->, ⊙, I])
    def idlK[F[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[I[a], F[a]] -> F[a]] =
      a.idl[TypeK[F]].unapply
    def coidlK[F[_]](using IsInjective2[⊙]): ∀[[a] =>> F[a] -> ⊙[I[a], F[a]]] =
      a.coidl[TypeK[F]].unapply
    def idrK[F[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[F[a], I[a]] -> F[a]] =
      a.idr[TypeK[F]].unapply
    def coidrK[F[_]](using IsInjective2[⊙]): ∀[[a] =>> F[a] -> ⊙[F[a], I[a]]] =
      a.coidr[TypeK[F]].unapply

}

trait MonoidalInstances {
  // TODO: de facut
}