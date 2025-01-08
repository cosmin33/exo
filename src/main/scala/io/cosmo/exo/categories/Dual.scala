package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.internal.*

opaque type Dual[->[_,_], A, B] <: B -> A = B -> A

object Dual:
  
  def apply[->[_,_], A, B](f: B -> A): Dual[->, A, B] = f
  def forall[->[_,_], F[_], G[_]](f: ∀[[a] =>> G[a] -> F[a]]): ∀[[a] =>> Dual[->, F[a], G[a]]] = f
  def forall2[->[_,_], F[_,_], G[_,_]](f: ∀∀[[a, b] =>> G[a, b] -> F[a, b]]): ∀∀[[a, b] =>> Dual[->, F[a, b], G[a, b]]] = f
  def forallK[->[_,_], F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> G[a] -> F[a]]): ∀~[[a[_]] =>> Dual[->, F[a], G[a]]] = f

  def leibniz[->[_,_]]: Opp[->] =~~= Dual[->,*,*] = IsK2.refl
  def is[->[_,_], A, B]: (B -> A) === Dual[->, A, B] = leibniz[->].is[A, B]

  extension [->[_,_], A, B](self: Dual[->, A, B])
    def toFn: B -> A = self
  extension[->[_,_], F[_], G[_]](self: ∀[[a] =>> Dual[->, F[a], G[a]]])
    def toFnK: ∀[[a] =>> G[a] -> F[a]] = ∀[[a] =>> G[a] -> F[a]](self.apply)
  extension[->[_,_], F[_,_], G[_,_]](self: ∀∀[[a, b] =>> Dual[->, F[a, b], G[a, b]]])
    def toFnK2: ∀∀[[a, b] =>> G[a, b] -> F[a, b]] = ∀∀[[a, b] =>> G[a, b] -> F[a, b]](self.apply)
  extension[->[_,_], A[_[_]], B[_[_]]](self: ∀~[[a[_]] =>> Dual[->, A[a], B[a]]])
    def toFnH: ∀~[[a[_]] =>> B[a] -> A[a]] = ∀~[[a[_]] =>> B[a] -> A[a]](self.apply)
  
  given nestedDualCancelsItself[->[_,_]]: (Dual[Dual[->,*,*],*,*] =~~= ->) =
    Dual.leibniz[->].subst[[f[_,_]] =>> Opp[Opp[->]] =~~= Dual[f, *, *]](Dual.leibniz[Opp[->]]).flip
  
end Dual
