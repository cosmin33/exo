package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

trait Symmetric[->[_,_], ⊙[_,_]] extends Braided[->, ⊙]:
  def swap[A: TC, B: TC]: ⊙[A, B] -> ⊙[B, A] = braid

  private type <->[a, b] = Iso[->, a, b]
  def isoSymmetric[A: TC, B: TC]: ⊙[A, B] <-> ⊙[B, A] = Iso.unsafe(swap[A, B], swap[B, A])(using C)
end Symmetric

object Symmetric:
  def apply[->[_,_], ⊙[_,_]](using ev: Symmetric[->, ⊙]): Symmetric[->, ⊙] = ev
  type Aux[->[_,_], ⊙[_,_], TC0[_]] = Symmetric[->, ⊙] {type TC[a] = TC0[a]}
  type AuxT[->[_,_], ⊙[_,_]] = Aux[->, ⊙, Trivial]
  trait Proto[->[_,_], ⊙[_,_], TC0[_]] extends Symmetric[->, ⊙] { type TC[a] = TC0[a] }

  extension[->[_,_], ⊙[_,_]](a: SymmetricK[->, ⊙])
    def swapK[F[_], G[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[F[a], G[a]] -> ⊙[G[a], F[a]]] =
      a.swap[TypeK[F], TypeK[G]].unapply
    def isoSymmetricK[F[_], G[_]](using IsInjective2[⊙], Subcat[->]): IsoK[->, [a] =>> ⊙[F[a], G[a]], [a] =>> ⊙[G[a], F[a]]] =
      IsoK.unsafe(swapK, swapK)

end Symmetric
