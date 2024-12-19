package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

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
  with EvidenceCatAssocInstances
  with ProdcatAssociativeInstances {

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

  extension[->[_,_], ⊙[_,_]](a: AssociativeK[->, ⊙])
    def associateK[F[_], G[_], H[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[⊙[F[a], G[a]], H[a]] -> ⊙[F[a], ⊙[G[a], H[a]]]] =
      a.associate[TypeK[F], TypeK[G], TypeK[H]].unapply
    def diassociateK[F[_], G[_], H[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[F[a], ⊙[G[a], H[a]]] -> ⊙[⊙[F[a], G[a]], H[a]]] =
      a.diassociate[TypeK[F], TypeK[G], TypeK[H]].unapply
    def groupedK[F[_], G[_], X[_], Y[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> X[a] -> Y[a]])(using IsInjective2[⊙])
    : ∀[[a] =>> ⊙[F[a], X[a]] -> ⊙[G[a], Y[a]]] =
      a.grouped[TypeK[F], TypeK[G], TypeK[X], TypeK[Y]](ArrowK(f), ArrowK(g)).unapply
    def isoAssociatorK[F[_], G[_], H[_]](using IsInjective2[⊙], Subcat[->])
    : IsoK[->, [a] =>> ⊙[⊙[F[a], G[a]], H[a]], [a] =>> ⊙[F[a], ⊙[G[a], H[a]]]] = IsoK.unsafe(associateK, diassociateK)

}

object AssociativeK {
  trait Proto[->[_,_], ⊙[_,_]] extends Associative[ArrowK[->,*,*], ⊙] {
    given inj: IsInjective2[⊙]
    given sub: Subcategory.Aux[->, Trivial]
    type TC[a] = IsKind[a]
    def C: Subcategory.Aux[ArrowK[->,*,*], IsKind] = summon
    def bifunctor: Endobifunctor[ArrowK[->,*,*], ⊙] = ???
    def associateK  [F[_], G[_], H[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[⊙[F[a], G[a]], H[a]] -> ⊙[F[a], ⊙[G[a], H[a]]]]
    def diassociateK[F[_], G[_], H[_]](using IsInjective2[⊙]): ∀[[a] =>> ⊙[F[a], ⊙[G[a], H[a]]] -> ⊙[⊙[F[a], G[a]], H[a]]]
    def associate[X: IsKind, Y: IsKind, Z: IsKind]: ArrowK[->, X ⊙ Y ⊙ Z, X ⊙ (Y ⊙ Z)] =
      ArrowK.from[->, X ⊙ Y ⊙ Z, X ⊙ (Y ⊙ Z)](associateK)
    def diassociate[X: IsKind, Y: IsKind, Z: IsKind]: ArrowK[->, X ⊙ (Y ⊙ Z), X ⊙ Y ⊙ Z] =
      ArrowK.from[->, X ⊙ (Y ⊙ Z), X ⊙ Y ⊙ Z](diassociateK)
  }
}

trait AssociativeImplicits {
}

object AssociativeHelpers

end AssociativeHelpers
