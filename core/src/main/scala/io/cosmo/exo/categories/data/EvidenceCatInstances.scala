package io.cosmo.exo.categories.data

import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.{Exobifunctor, LaxSemigroupal}
import io.cosmo.exo.evidence.=~~=
import io.cosmo.exo.{/\, Void, \/}
import io.cosmo.exo.internal.any._

object EvidenceCatInstances extends EvidenceCatInstances

trait EvidenceCatInstances extends EvidenceCatInstances01 {

  type First [T[_], A, B] = T[A]
  type Second[T[_], A, B] = T[B]

  def bifunctorStartTup[T[_]](implicit L: LaxSemigroupal[(*, *), * => *, (*, *), T]): Endobifunctor[λ[(a,b) => T[a]], (*, *)] =
    new Endobifunctor[λ[(a,b) => T[a]], (*, *)] {
      def bimap[A, X, B, Y](l: T[A], r: T[B]) = L.product((l, r))
    }

  implicit def bifunctorStartConj[T[_]](implicit L: LaxSemigroupal[/\, * => *, /\, T]): Endobifunctor[λ[(a,b) => T[a]], /\] =
    new Endobifunctor[λ[(a,b) => T[a]], /\] {
      def bimap[A, X, B, Y](l: T[A], r: T[B]) = L.product((l, r))
    }
  
  implicit def bifunctorEndTup[T[_]](implicit L: LaxSemigroupal[(*,*), * => *, (*,*), T]): Endobifunctor[λ[(a,b) => T[b]], (*,*)] =
    new Endobifunctor[λ[(a,b) => T[b]], (*,*)] {
      def bimap[A, X, B, Y](l: T[X], r: T[Y])= L.product((l, r))
    }

  implicit def bifunctorEndConj[T[_]](implicit L: LaxSemigroupal[/\, * => *, /\, T]): Endobifunctor[λ[(a,b) => T[b]], /\] =
    new Endobifunctor[λ[(a,b) => T[b]], /\] {
      def bimap[A, X, B, Y](l: T[X], r: T[Y])= L.product((l, r))
    }

  implicit def bifunctorStartDisj[T[_]](implicit L: LaxSemigroupal[\/, * => *, /\, T]): Endobifunctor[λ[(a,b) => T[a]], \/] =
    new Endobifunctor[λ[(a,b) => T[a]], \/] {
      def bimap[A, X, B, Y](l: T[A], r: T[B]) = L.product((l, r))
    }

  implicit def bifunctorEndDisj[T[_]](implicit L: LaxSemigroupal[\/, * => *, /\, T]): Endobifunctor[λ[(a,b) => T[b]], \/] =
    new Endobifunctor[λ[(a,b) => T[b]], \/] {
      def bimap[A, X, B, Y](l: T[X], r: T[Y]) = L.product((l, r))
    }

  implicit def cartesianStartConj[T[_]](implicit
    L: LaxSemigroupal[/\, * => *, /\, T], ti: T[Unit]
  ): Cartesian.Aux[EvidenceStart[T,*,*], /\, T, Unit] =
    new Cartesian[EvidenceStart[T,*,*], /\] {
      type TC[a] = T[a]
      type Id = Unit
      def C = categoryStart
      def bifunctor = bifunctorStartConj
      def fst[A: TC, B: TC]                = implicitly
      def snd[A: TC, B: TC]                = implicitly
      def diag [A: TC]                     = implicitly
      def idl  [A: TC]                     = implicitly
      def coidl[A: TC]                     = implicitly
      def idr  [A: TC]                     = implicitly
      def coidr[A: TC]                     = implicitly
      def braid[A: TC, B: TC]              = implicitly
      def associate[X: TC, Y: TC, Z: TC]   = implicitly
      def diassociate[X: TC, Y: TC, Z: TC] = implicitly
      def &&&[X, Y, Z](f: EvidenceStart[T, X, Y], g: EvidenceStart[T, X, Z]) = f
    }

  implicit def cartesianEndConj[T[_]](implicit
    L: LaxSemigroupal[/\, * => *, /\, T], ti: T[Unit]
  ): Cartesian.Aux[EvidenceEnd[T,*,*], /\, T, Unit] =
    new Cartesian[EvidenceEnd[T,*,*], /\] {
      type TC[a] = T[a]
      type Id = Unit
      def C = categoryEnd
      def bifunctor = bifunctorEndConj
      def fst[A: TC, B: TC]                = implicitly
      def snd[A: TC, B: TC]                = implicitly
      def diag [A: TC]                     = implicitly
      def idl  [A: TC]                     = implicitly
      def coidl[A: TC]                     = implicitly
      def idr  [A: TC]                     = implicitly
      def coidr[A: TC]                     = implicitly
      def braid[A: TC, B: TC]              = implicitly
      def associate[X: TC, Y: TC, Z: TC]   = implicitly
      def diassociate[X: TC, Y: TC, Z: TC] = implicitly
      def &&&[X, Y, Z](f: EvidenceEnd[T, X, Y], g: EvidenceEnd[T, X, Z]): T[Y /\ Z] = bifunctor.bimap(f, g)
    }

  private def proveEquality1[T[_]] = implicitly[Opp[EvidenceStart[T,*,*]]#l =~~= EvidenceEnd[T,*,*]]
  private def proveEquality2[T[_]] = implicitly[Opp[EvidenceEnd[T,*,*]]#l =~~= EvidenceStart[T,*,*]]

  implicit def cartesianStartDisj[T[_]](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[Void]
  ): Cartesian.Aux[EvidenceStart[T,*,*], \/, T, Void] =
    new Cartesian[EvidenceStart[T,*,*], \/] {
      type TC[a] = T[a]
      type Id = Void
      def C = DualModule.oppSubcat(categoryEnd[T])
      def bifunctor = Exobifunctor.opp(bifunctorEndDisj)
      def fst[A: TC, B: TC]                = implicitly
      def snd[A: TC, B: TC]                = implicitly
      def diag[A: TC]                      = implicitly
      def braid[A: TC, B: TC]              = implicitly
      def idl[A: TC]                       = implicitly
      def coidl[A: TC]                     = implicitly
      def idr[A: TC]                       = implicitly
      def coidr[A: TC]                     = implicitly
      def associate[X: TC, Y: TC, Z: TC]   = implicitly
      def diassociate[X: TC, Y: TC, Z: TC] = implicitly
      def &&&[X, Y, Z](f: EvidenceStart[T, X, Y], g: EvidenceStart[T, X, Z]) = f
    }

  implicit def cartesianEndDisj[T[_]](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[Void]
  ): Cartesian.Aux[EvidenceEnd[T,*,*], \/, T, Void] =
    new Cartesian[EvidenceEnd[T,*,*], \/] {
      type TC[a] = T[a]
      type Id = Void
      def C = DualModule.oppSubcat(categoryStart[T])
      def bifunctor = Exobifunctor.opp(bifunctorStartDisj)
      def fst[A: TC, B: TC]                = implicitly
      def snd[A: TC, B: TC]                = implicitly
      def diag[A: TC]                      = implicitly
      def idl  [A: TC]                     = implicitly
      def coidl[A: TC]                     = implicitly
      def idr  [A: TC]                     = implicitly
      def coidr[A: TC]                     = implicitly
      def braid[A: TC, B: TC]              = implicitly
      def associate  [X: TC, Y: TC, Z: TC] = implicitly
      def diassociate[X: TC, Y: TC, Z: TC] = implicitly
      def &&&[X, Y, Z](f: EvidenceEnd[T, X, Y], g: EvidenceEnd[T, X, Z]) = bifunctor.bimap(f, g)
    }

  implicit def cocartesianStartDisj[T[_]](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[Void]
  ): Cocartesian.Aux[EvidenceStart[T,*,*], \/, T, Void] =
    cartesianEndDisj(L, ti) |> Dual.leibniz[EvidenceStart[T,*,*]].subst[Cartesian.Aux[*[_,_], \/, T, Void]]

  implicit def cocartesianEndDisj[T[_]](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[Void]
  ): Cocartesian.Aux[EvidenceEnd[T,*,*], \/, T, Void] =
    cartesianStartDisj(L, ti) |> Dual.leibniz[EvidenceEnd[T,*,*]].subst[Cartesian.Aux[*[_,_], \/, T, Void]]

  implicit def distributiveStart[T[_]](implicit
    L1: LaxSemigroupal[/\, * => *, /\, T],
    L2: LaxSemigroupal[\/, * => *, /\, T],
    tpi: T[Unit],
    tsi: T[Void],
  ): Distributive.Aux[EvidenceStart[T,*,*], T, /\, Unit, \/, Void] =
    new Distributive[EvidenceStart[T,*,*], /\, \/] {
      type TC[a] = T[a]
      type ProductId = Unit
      type SumId = Void
      def cartesian = implicitly
      def cocartesian = implicitly
      def distribute[A: TC, B: TC, C: TC] = implicitly
      def id[A: TC] = implicitly
      def andThen[A, B, C](ab: EvidenceStart[T, A, B], bc: EvidenceStart[T, B, C]) = ab
    }

  implicit def distributiveEnd[T[_]](implicit
    L1: LaxSemigroupal[/\, * => *, /\, T],
    L2: LaxSemigroupal[\/, * => *, /\, T],
    tpi: T[Unit],
    tsi: T[Void],
  ): Distributive.Aux[EvidenceEnd[T,*,*], T, /\, Unit, \/, Void] =
    new Distributive[EvidenceEnd[T,*,*], /\, \/] {
      type TC[a] = T[a]
      type ProductId = Unit
      type SumId = Void
      def cartesian = implicitly
      def cocartesian = implicitly
      def distribute[A: TC, B: TC, C: TC] = implicitly
      def id[A](implicit A: TC[A]): EvidenceEnd[T, A, A] = implicitly
      def andThen[A, B, C](ab: EvidenceEnd[T, A, B], bc: EvidenceEnd[T, B, C]) = bc
    }

  def cartesianSameConj[T[_]](implicit
    L: LaxSemigroupal[/\, * => *, /\, T], ti: T[Unit]
  ): Cartesian.Aux[EvidenceSame[T,*,*], /\, T, Unit] = prodcatCartesian(cartesianStartConj, cartesianEndConj)

  def cartesianSameDisj[T[_]](implicit
    L: LaxSemigroupal[\/, * => *, /\, T], ti: T[Void]
  ): Cartesian.Aux[EvidenceSame[T,*,*], \/, T, Void] = prodcatCartesian(cartesianStartDisj, cartesianEndDisj)

  def distributiveSame[T[_]](implicit
    L1: LaxSemigroupal[/\, * => *, /\, T],
    L2: LaxSemigroupal[\/, * => *, /\, T],
    tpi: T[Unit],
    tsi: T[Void],
  ): Distributive.Aux[EvidenceSame[T,*,*], T, /\, Unit, \/, Void] = prodcatDistributive(distributiveStart, distributiveEnd)

}

trait EvidenceCatInstances01 {
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

}
