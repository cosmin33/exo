package io.cosmo.exo.categories.data

import io.cosmo.exo
import io.cosmo.exo.{/\, \/}
import io.cosmo.exo.categories.functors.{Exobifunctor, LaxSemigroupal}
import io.cosmo.exo.categories.{Cartesian, Cocartesian, Distributive, Dual, DualModule, Endobifunctor, Opp, Subcat}
import io.cosmo.exo.evidence.=~~=
import mouse.any._

object EvidenceCatInstances {

  def categoryStart[T[_]]: Subcat.Aux[λ[(a,b) => T[a]], T] =
    new Subcat[λ[(a,b) => T[a]]] {
      type TC[a] = T[a]
      def id[A](implicit a: TC[A]) = a
      def andThen[A, B, C](ab: T[A], bc: T[B]) = ab
    }

  def categoryEnd[T[_]]: Subcat.Aux[λ[(a,b) => T[b]], T] =
    new Subcat[λ[(a,b) => T[b]]] {
      type TC[a] = T[a]
      def id[A](implicit A: TC[A]): T[A] = A
      def andThen[A, B, C](ab: T[B], bc: T[C]): T[C] = bc
    }

  def bifunctorStartTup[T[_]](implicit L: LaxSemigroupal[(*, *), * => *, (*, *), T]): Endobifunctor[EvidenceStart[T,*,*], (*, *)] =
    new Endobifunctor[EvidenceStart[T,*,*], (*, *)] {
      def bimap[A, X, B, Y](l: EvidenceStart[T, A, X], r: EvidenceStart[T, B, Y]) = L.product[A, B]((l, r))
    }

  implicit def bifunctorStartConj[T[_]](implicit L: LaxSemigroupal[/\, * => *, /\, T]): Endobifunctor[EvidenceStart[T,*,*], /\] =
    new Endobifunctor[EvidenceStart[T,*,*], /\] {
      def bimap[A, X, B, Y](l: EvidenceStart[T, A, X], r: EvidenceStart[T, B, Y]) = L.product[A, B](/\(l, r))
    }

  implicit def bifunctorEndConj[T[_]](implicit L: LaxSemigroupal[/\, * => *, /\, T]): Endobifunctor[EvidenceEnd[T,*,*], /\] =
    new Endobifunctor[EvidenceEnd[T,*,*], /\] {
      def bimap[A, X, B, Y](l: EvidenceEnd[T, A, X], r: EvidenceEnd[T, B, Y])= L.product[X, Y](/\(l, r))
    }

  implicit def bifunctorStartDisj[T[_]](implicit L: LaxSemigroupal[\/, * => *, /\, T]): Endobifunctor[EvidenceStart[T,*,*], \/] =
    new Endobifunctor[EvidenceStart[T,*,*], \/] {
      def bimap[A, X, B, Y](l: EvidenceStart[T, A, X], r: EvidenceStart[T, B, Y]) = L.product(/\(l, r))
    }

  implicit def bifunctorEndDisj[T[_]](implicit L: LaxSemigroupal[\/, * => *, /\, T]): Endobifunctor[EvidenceEnd[T,*,*], \/] =
    new Endobifunctor[EvidenceEnd[T,*,*], \/] {
      def bimap[A, X, B, Y](l: EvidenceEnd[T, A, X], r: EvidenceEnd[T, B, Y]) = L.product(/\(l, r))
    }

  implicit def cartesianStartConj[T[_], I](implicit
    L: LaxSemigroupal[/\, * => *, /\, T], ti: T[I]
  ): Cartesian.Aux[EvidenceStart[T,*,*], /\, T, I] =
    new Cartesian[EvidenceStart[T,*,*], /\] {
      type TC[a] = T[a]
      type Id = I
      def C = categoryStart
      def bifunctor = bifunctorStartConj
      def fst[A: TC, B: TC] = implicitly
      def snd[A: TC, B: TC] = implicitly
      def diag [A: TC] = implicitly
      def idl  [A: TC] = implicitly
      def coidl[A: TC] = implicitly
      def idr  [A: TC] = implicitly
      def coidr[A: TC] = implicitly
      def braid[A: TC, B: TC] = implicitly
      def associate[X: TC, Y: TC, Z: TC] = implicitly
      def diassociate[X: TC, Y: TC, Z: TC] = implicitly
      def &&&[X, Y, Z](f: EvidenceStart[T, X, Y], g: EvidenceStart[T, X, Z]) = f
    }

  implicit def cartesianEndConj[T[_], I](implicit
    L: LaxSemigroupal[/\, * => *, /\, T], ti: T[I]
  ): Cartesian.Aux[EvidenceEnd[T,*,*], /\, T, I] =
    new Cartesian[EvidenceEnd[T,*,*], /\] {
      type TC[a] = T[a]
      type Id = I
      def C = categoryEnd
      def bifunctor = bifunctorEndConj
      def fst[A: TC, B: TC] = implicitly
      def snd[A: TC, B: TC] = implicitly
      def diag [A: TC] = implicitly
      def idl  [A: TC] = implicitly
      def coidl[A: TC] = implicitly
      def idr  [A: TC] = implicitly
      def coidr[A: TC] = implicitly
      def braid[A: TC, B: TC] = implicitly
      def associate[X: TC, Y: TC, Z: TC] = implicitly
      def diassociate[X: TC, Y: TC, Z: TC] = implicitly
      def &&&[X, Y, Z](f: EvidenceEnd[T, X, Y], g: EvidenceEnd[T, X, Z]): T[Y /\ Z] = L.product[Y, Z](/\(f, g))
    }

  def proveEquality[T[_]] = implicitly[Opp[EvidenceStart[T,*,*]]#l =~~= EvidenceEnd[T,*,*]]

  def cocartesianStartDisjOpp[T[_], I](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[I]
  ): Cartesian.Aux[EvidenceEnd[T,*,*], \/, T, I] =
    new Cartesian[EvidenceEnd[T,*,*], \/] {
      type TC[a] = T[a]
      type Id = I
      def C = DualModule.oppSubcat(categoryStart[T])
      def bifunctor = Exobifunctor.opp(bifunctorStartDisj)
      def fst[A: TC, B: TC] = implicitly
      def snd[A: TC, B: TC] = implicitly
      def diag[A: TC]: T[A \/ A] = implicitly
      def idl  [A: TC] = implicitly
      def coidl[A: TC] = implicitly
      def idr  [A: TC] = implicitly
      def coidr[A: TC] = implicitly
      def braid[A: TC, B: TC]: T[B \/ A] = implicitly
      def associate  [X: TC, Y: TC, Z: TC]: T[X \/ (Y \/ Z)] = implicitly
      def diassociate[X: TC, Y: TC, Z: TC]: T[(X \/ Y) \/ Z] = implicitly
      def &&&[X, Y, Z](f: EvidenceEnd[T, X, Y], g: EvidenceEnd[T, X, Z]) = L.product(/\(f, g))
    }

  implicit def cocartesianStartDisj[T[_], I](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[I]
  ): Cartesian.Aux[Dual[EvidenceStart[T,*,*], *, *], \/, T, I] =
    cocartesianStartDisjOpp(L, ti) |> Dual.leibniz[EvidenceStart[T,*,*]].subst[Cartesian.Aux[*[_,_], \/, T, I]]

  def cocartesianEndDisjOpp[T[_], I](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[I]
  ): Cartesian.Aux[EvidenceEnd[T,*,*], \/, T, I] =
    new Cartesian[EvidenceEnd[T,*,*], \/] {
      type TC[a] = T[a]
      type Id = I
      def C = categoryEnd[T]
      def bifunctor = bifunctorEndDisj
      def fst[A: TC, B: TC] = implicitly
      def snd[A: TC, B: TC] = implicitly
      def diag[A: TC]: T[A \/ A] = implicitly
      def idl  [A: TC] = implicitly
      def coidl[A: TC] = implicitly
      def idr  [A: TC] = implicitly
      def coidr[A: TC] = implicitly
      def braid[A: TC, B: TC]: T[B \/ A] = implicitly
      def associate  [X: TC, Y: TC, Z: TC]: T[X \/ (Y \/ Z)] = implicitly
      def diassociate[X: TC, Y: TC, Z: TC]: T[(X \/ Y) \/ Z] = implicitly
      def &&&[X, Y, Z](f: EvidenceEnd[T, X, Y], g: EvidenceEnd[T, X, Z]) = L.product(/\(f, g))
    }

  implicit def cocartesianEndDisj[T[_], I](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[I]
  ): Cartesian.Aux[Dual[EvidenceEnd[T,*,*], *, *], \/, T, I] =
    ??? //cocartesianEndDisjOpp(L, ti) |> Dual.leibniz[EvidenceEnd[T,*,*]].subst[Cartesian.Aux[*[_,_], \/, T, I]]

  implicit def distributiveStart[T[_], PI, SI](implicit
    L1: LaxSemigroupal[/\, * => *, /\, T],
    L2: LaxSemigroupal[\/, * => *, /\, T],
    tsi: T[PI],
    tpi: T[SI],
  ): Distributive.Aux[EvidenceStart[T,*,*], T, /\, PI, \/, SI] =
    new Distributive[EvidenceStart[T,*,*], /\, \/] {
      type TC[a] = T[a]
      type ProductId = PI
      type SumId = SI
      def cartesian = cartesianStartConj
      def cocartesian = cocartesianStartDisj(L2, tpi)
      def distribute[A: TC, B: TC, C: TC] = implicitly
      def id[A: TC] = implicitly
      def andThen[A, B, C](ab: EvidenceStart[T, A, B], bc: EvidenceStart[T, B, C]) = ab
    }

}
