package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.functors._
import io.cosmo.exo.evidence._
import io.cosmo.exo.internal._

trait Associative[->[_, _], ⊙[_, _]] {
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [X: TC, Y: TC, Z: TC]: ⊙[⊙[X, Y], Z] -> ⊙[X, ⊙[Y, Z]]
  def diassociate[X: TC, Y: TC, Z: TC]: ⊙[X, ⊙[Y, Z]] -> ⊙[⊙[X, Y], Z]

  def grouped[A, B, X, Y](f: A -> B, g: X -> Y): ⊙[A, X] -> ⊙[B, Y] = bifunctor.bimap(f, g)

  def strongFirst [A, B, C: TC](fa: A -> B): ⊙[C, A] -> ⊙[C, B] = grouped(C.id[C], fa)
  def strongSecond[A, B, C: TC](fa: A -> B): ⊙[A, C] -> ⊙[B, C] = grouped(fa, C.id[C])

  private type <->[a, b] = Iso[->, a, b]
  def isoAssociator[X: TC, Y: TC, Z: TC]: ⊙[⊙[X, Y], Z] <-> ⊙[X, ⊙[Y, Z]] = Iso.unsafe(associate[X,Y,Z], diassociate[X,Y,Z])(using C)
}

object Associative extends Function1AssociativeInstances 
  with DualAssociativeInstances 
  with EvidenceCatAssocInstances {
  type Aux[->[_, _], ⊙[_, _], TC0[_]] = Associative[->, ⊙] {type TC[a] = TC0[a]}
  trait Proto[->[_, _], ⊙[_, _], TC0[_]] extends Associative[->, ⊙] { type TC[A] = TC0[A] }

  def apply[->[_,_], ⊙[_,_]](using assoc: Associative[->, ⊙]): Associative.Aux[->, ⊙, assoc.TC] = assoc

  def fromIso[->[_,_], ⊙[_,_], Tc[_]](i: ∀∀∀[[a,b,c] =>> Iso[->, ⊙[⊙[a, b], c], ⊙[a, ⊙[b, c]]]])(
    using cat: Subcat.Aux[->, Tc], bif: Endobifunctor[->, ⊙]
  ): Associative.Aux[->, ⊙, Tc] =
    new Associative.Proto[->, ⊙, Tc]:
      val C = cat
      val bifunctor = bif
      def associate  [X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].to
      def diassociate[X: TC, Y: TC, Z: TC] = i.apply[X, Y, Z].from

}
