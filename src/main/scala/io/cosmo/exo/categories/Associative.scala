package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

trait Associative[->[_,_], ⊙[_,_]]:
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [A: TC, B: TC, C: TC]: ⊙[⊙[A, B], C] -> ⊙[A, ⊙[B, C]]
  def diassociate[A: TC, B: TC, C: TC]: ⊙[A, ⊙[B, C]] -> ⊙[⊙[A, B], C]

  def grouped[A, B, X, Y](f: A -> B, g: X -> Y): ⊙[A, X] -> ⊙[B, Y] = bifunctor.bimap(f, g)

  def strongFirst [A, B, C: TC](fa: A -> B): ⊙[C, A] -> ⊙[C, B] = grouped(C.id[C], fa)
  def strongSecond[A, B, C: TC](fa: A -> B): ⊙[A, C] -> ⊙[B, C] = grouped(fa, C.id[C])

  private type <->[a, b] = Iso[->, a, b]
  def isoAssociator[A: TC, B: TC, C: TC]: ⊙[⊙[A, B], C] <-> ⊙[A, ⊙[B, C]] = Iso.unsafe(associate[A,B,C], diassociate[A,B,C])(using C)

object Associative extends Function1AssociativeInstances 
  with DualAssociativeInstances 
  with EvidenceCatAssocInstances
  with ProdcatAssociativeInstances:

  type Aux[->[_,_], ⊙[_,_], TC0[_]] = Associative[->, ⊙] {type TC[a] = TC0[a]}
  trait Proto[->[_,_], ⊙[_,_], TC0[_]] extends Associative[->, ⊙] { type TC[A] = TC0[A] }

  def apply[->[_,_], ⊙[_,_]](using assoc: Associative[->, ⊙]): Associative.Aux[->, ⊙, assoc.TC] = assoc

  def fromIso[->[_,_], ⊙[_,_], Tc[_]](i: ∀∀∀[[a,b,c] =>> Iso[->, ⊙[⊙[a, b], c], ⊙[a, ⊙[b, c]]]])(
    using cat: Subcat.Aux[->, Tc], bif: Endobifunctor[->, ⊙]
  ): Associative.Aux[->, ⊙, Tc] =
    new Associative.Proto[->, ⊙, Tc]:
      val C = cat
      val bifunctor = bif
      def associate  [X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].to
      def diassociate[X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].from

private trait AssociativeImplicits {
}

private object AssociativeHelpers

end AssociativeHelpers

