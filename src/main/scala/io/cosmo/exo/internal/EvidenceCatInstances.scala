package io.cosmo.exo.internal

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.Conjunction.given
import io.cosmo.exo.Disjunction.given

import EvidenceCatHelpers.*

type First [T[_], A, B] = T[A]
type Second[T[_], A, B] = T[B]

trait EvidenceCatBifunctorInstances {
  given firstCatBifunctorConj [T[_]](using L: LaxSemigroupal[/\, Function, /\, T]): Endobifunctor[First[T, *, *], /\] =
    new Endobifunctor[First[T, *, *], /\]:
      def bimap[A, B, C, D](a: T[A], b: T[C]): T[A /\ C] = L.product((a, b))
  given firstCatBifunctorDisj [T[_]](using L: LaxSemigroupal[\/, Function, \/, T]): Endobifunctor[First[T, *, *], \/] =
    new Endobifunctor[First[T, *, *], \/]:
      def bimap[A, B, C, D](a: T[A], b: T[C]): T[A \/ C] = L.product(-\/(a))
  given secondCatBifunctorConj[T[_]](using L: LaxSemigroupal[/\, Function, /\, T]): Endobifunctor[Second[T, *, *], /\] =
    new Endobifunctor[Second[T, *, *], /\]:
      def bimap[A, B, C, D](a: T[B], b: T[D]): T[B /\ D] = L.product((a, b))
  given secondCatBifunctorDisj[T[_]](using L: LaxSemigroupal[\/, Function, \/, T]): Endobifunctor[Second[T, *, *], \/] =
    new Endobifunctor[Second[T, *, *], \/]:
      def bimap[A, B, C, D](a: T[B], b: T[D]): T[B \/ D] = L.product(-\/(a))
}

trait EvidenceCatSubcatInstances extends EvidenceCatSubcatInstances01 {
  given firstCatSubcat [T[_]]: Subcat.Aux[First [T,*,*], T] = new FirstSubcat[T] {}
  given secondCatSubcat[T[_]]: Subcat.Aux[Second[T,*,*], T] = new SecondSubcat[T] {}
}
trait EvidenceCatSubcatInstances01 {
  given firstCatDistributive[T[_]](using
    lc: LaxSemigroupal[/\, Function, /\, T],
    ld: LaxSemigroupal[\/, Function, \/, T],
    tp: T[Unit],
    ts: T[Void]
  ): Distributive.Aux[First[T,*,*], T, /\, Unit, \/, Void] =
    new FirstDistributive[T] { val LC = lc; val LD = ld; val TP = tp; val TS = ts }
  given secondCatDistributive[T[_]](using
    lc: LaxSemigroupal[/\, Function, /\, T],
    ld: LaxSemigroupal[\/, Function, \/, T],
    tp: T[Unit],
    ts: T[Void]
  ): Distributive.Aux[Second[T,*,*], T, /\, Unit, \/, Void] =
    new SecondDistributive[T] { val LC = lc; val LD = ld; val TP = tp; val TS = ts }
}

trait EvidenceCatAssocInstances extends EvidenceCatAssocInstances01 {
  given firstCatAssociativeConj [T[_]](using l: LaxSemigroupal[/\, Function, /\, T]): Associative.Aux[First[T,*,*], /\, T] =
    new FirstAssociativeConj[T] { val L = l }
  given firstCatAssociativeDisj [T[_]](using l: LaxSemigroupal[\/, Function, \/, T]): Associative.Aux[First[T,*,*], \/, T] =
    new FirstAssociativeDisj[T] { val L = l }
  given secondCatAssociativeConj[T[_]](using l: LaxSemigroupal[/\, Function, /\, T]): Associative.Aux[Second[T,*,*], /\, T] =
    new SecondAssociativeConj[T] { val L = l }
  given secondCatAssociativeDisj[T[_]](using l: LaxSemigroupal[\/, Function, \/, T]): Associative.Aux[Second[T,*,*], \/, T] =
    new SecondAssociativeDisj[T] { val L = l }
}

trait EvidenceCatAssocInstances01 {
  given firstCatCartesianConj [T[_]](using l: LaxSemigroupal[/\, Function, /\, T], u: T[Unit]): Cartesian.Aux[First[T,*,*], /\, T, Unit] =
    new FirstCartesianConj[T] { val L = l; val TU = u }
  given firstCatCartesianDisj [T[_]](using l: LaxSemigroupal[\/, Function, \/, T], u: T[Void]): Cartesian.Aux[First[T,*,*], \/, T, Void] =
    new FirstCartesianDisj[T] { val L = l; val TU = u }
  given secondCatCartesianConj[T[_]](using l: LaxSemigroupal[/\, Function, /\, T], u: T[Unit]): Cartesian.Aux[Second[T,*,*], /\, T, Unit] =
    new SecondCartesianConj[T] { val L = l; val TU = u }
  given secondCatCartesianDisj[T[_]](using l: LaxSemigroupal[\/, Function, \/, T], u: T[Void]): Cartesian.Aux[Second[T,*,*], \/, T, Void] =
    new SecondCartesianDisj[T] { val L = l; val TU = u }
  given firstCatCocartesianConj [T[_]](using LaxSemigroupal[/\, Function, /\, T], T[Unit]): Cocartesian.Aux[First[T,*,*], /\, T, Unit] =
    Dual.leibniz[First[T,*,*]].subst[[f[_,_]] =>> Cartesian.Aux[f, /\, T, Unit]](secondCatCartesianConj)
  given firstCatCocartesianDisj [T[_]](using LaxSemigroupal[\/, Function, \/, T], T[Void]): Cocartesian.Aux[First[T,*,*], \/, T, Void] =
    Dual.leibniz[First[T,*,*]].subst[[f[_,_]] =>> Cartesian.Aux[f, \/, T, Void]](secondCatCartesianDisj)
  given secondCatCocartesianConj[T[_]](using LaxSemigroupal[/\, Function, /\, T], T[Unit]): Cocartesian.Aux[Second[T,*,*], /\, T, Unit] =
    Dual.leibniz[Second[T,*,*]].subst[[f[_,_]] =>> Cartesian.Aux[f, /\, T, Unit]](firstCatCartesianConj)
  given secondCatCocartesianDisj[T[_]](using LaxSemigroupal[\/, Function, \/, T], T[Void]): Cocartesian.Aux[Second[T,*,*], \/, T, Void] =
    Dual.leibniz[Second[T,*,*]].subst[[f[_,_]] =>> Cartesian.Aux[f, \/, T, Void]](firstCatCartesianDisj)
}

trait EvidenceCatInitialInstances {
  given firstCatInitial[T[_]](using T: T[Void]): Initial.Aux[First[T,*,*], T, Void] =
    new Initial.Proto[First[T,*,*], T, Void]:
      def TC: T[Void] = T
      def subcat: Subcat.Aux[First[T,*,*], T] = summon
      def initiate[A](using A: T[A]): First[T, Void, A] = T
  given secondCatInitial[T[_]](using T: T[Unit]): Initial.Aux[Second[T,*,*], T, Unit] =
    new Initial.Proto[Second[T,*,*], T, Unit]:
      def TC: T[Unit] = T
      def subcat: Subcat.Aux[Second[T,*,*], T] = summon
      def initiate[A](using A: T[A]): Second[T, Unit, A] = A
  given firstCatTerminal[T[_]](using T: T[Unit]): Terminal.Aux[First[T,*,*], T, Unit] =
    Dual.leibniz[First[T,*,*]].subst[[f[_,_]] =>> Initial.Aux[f, T, Unit]](secondCatInitial[T])
  given secondCatTerminal[T[_]](using T: T[Void]): Terminal.Aux[Second[T,*,*], T, Void] =
    Dual.leibniz[Second[T,*,*]].subst[[f[_,_]] =>> Initial.Aux[f, T, Void]](firstCatInitial[T])
}

object EvidenceCatHelpers:
  trait FirstSubcat[T[_]] extends Subcat[First[T,*,*]]:
    type TC[A] = T[A]
    def id[A](using T: T[A]): T[A] = T
    def andThen[A, B, C](ab: T[A], bc: T[B]): T[A] = ab

  trait SecondSubcat[T[_]] extends Subcat[Second[T,*,*]]:
    type TC[A] = T[A]
    def id[A](using T: T[A]): T[A] = T
    def andThen[A, B, C](ab: T[B], bc: T[C]): T[C] = bc

  trait FirstDistributive[T[_]] extends Distributive.Proto[First[T,*,*], T, /\, Unit, \/, Void] with FirstSubcat[T]:
    given LC: LaxSemigroupal[/\, Function, /\, T]
    given LD: LaxSemigroupal[\/, Function, \/, T]
    given TP: T[Unit]
    given TS: T[Void]
    def cartesian: Cartesian.Aux[First[T,*,*], /\, T, Unit] = summon
    def cocartesian: Cocartesian.Aux[First[T,*,*], \/, T, Void] = summon
    def distribute[A: T, B: T, C: T]: T[A /\ (B \/ C)] = summon

  trait SecondDistributive[T[_]] extends Distributive.Proto[Second[T,*,*], T, /\, Unit, \/, Void] with SecondSubcat[T]:
    given LC: LaxSemigroupal[/\, Function, /\, T]
    given LD: LaxSemigroupal[\/, Function, \/, T]
    given TP: T[Unit]
    given TS: T[Void]
    def cartesian: Cartesian.Aux[Second[T,*,*], /\, T, Unit] = summon
    def cocartesian: Cocartesian.Aux[Second[T,*,*], \/, T, Void] = summon
    def distribute[A: T, B: T, C: T]: T[(A /\ B) \/ (A /\ C)] = summon

  trait FirstAssociativeConj[T[_]] extends Associative.Proto[First[T,*,*], /\, T]:
    given L: LaxSemigroupal[/\, Function, /\, T]
    def C: Subcat.Aux[First[T,*,*], T] = summon
    def bifunctor: Endobifunctor[First[T,*,*], /\] = summon
    def associate  [X: T, Y: T, Z: T]: T[(X /\ Y) /\ Z] = summon
    def diassociate[X: T, Y: T, Z: T]: T[X /\ (Y /\ Z)] = summon

  trait FirstCartesianConj[T[_]] extends Cartesian.Proto[First[T,*,*], /\, T, Unit] with FirstAssociativeConj[T]:
    given TU: T[Unit]
    def idl[A: T]: T[Unit /\ A] = summon
    def idr[A: T]: T[A /\ Unit] = summon
    def coidl[A: T]: T[A] = summon
    def coidr[A: T]: T[A] = summon
    def fst[A: T, B: T]: T[A /\ B] = summon
    def snd[A: T, B: T]: T[A /\ B] = summon
    def diag[A: T]: T[A] = summon
    def braid[A: T, B: T]: T[A /\ B] = summon
    def &&&[A, B, C](a: T[A], b: T[A]): T[A] = a

  trait FirstAssociativeDisj[T[_]] extends Associative.Proto[First[T,*,*], \/, T]:
    given L: LaxSemigroupal[\/, Function, \/, T]
    def C: Subcat.Aux[First[T,*,*], T] = summon
    def bifunctor: Endobifunctor[First[T,*,*], \/] = summon
    def associate  [X: T, Y: T, Z: T]: T[(X \/ Y) \/ Z] = summon
    def diassociate[X: T, Y: T, Z: T]: T[X \/ (Y \/ Z)] = summon

  trait FirstCartesianDisj[T[_]] extends Cartesian.Proto[First[T,*,*], \/, T, Void] with FirstAssociativeDisj[T]:
    given TU: T[Void]
    def idl[A: T]: T[Void \/ A] = summon
    def idr[A: T]: T[A \/ Void] = summon
    def coidl[A: T]: T[A] = summon
    def coidr[A: T]: T[A] = summon
    def fst[A: T, B: T]: T[A \/ B] = summon
    def snd[A: T, B: T]: T[A \/ B] = summon
    def diag[A: T]: T[A] = summon
    def braid[A: T, B: T]: T[A \/ B] = summon
    def &&&[A, B, C](a: T[A], b: T[A]): T[A] = a

  trait SecondAssociativeConj[T[_]] extends Associative.Proto[Second[T,*,*], /\, T]:
    given L: LaxSemigroupal[/\, Function, /\, T]
    def C: Subcat.Aux[Second[T,*,*], T] = summon
    def bifunctor: Endobifunctor[Second[T,*,*], /\] = summon
    def associate  [X: T, Y: T, Z: T]: T[X /\ (Y /\ Z)] = summon
    def diassociate[X: T, Y: T, Z: T]: T[(X /\ Y) /\ Z] = summon

  trait SecondCartesianConj[T[_]] extends Cartesian.Proto[Second[T,*,*], /\, T, Unit] with SecondAssociativeConj[T]:
    given TU: T[Unit]
    def idl[A: T]: T[A] = summon
    def idr[A: T]: T[A] = summon
    def coidl[A: T]: T[Unit /\ A] = summon
    def coidr[A: T]: T[A /\ Unit] = summon
    def fst[A: T, B: T]: T[A] = summon
    def snd[A: T, B: T]: T[B] = summon
    def diag[A: T]: T[A /\ A] = summon
    def braid[A: T, B: T]: T[B /\ A] = summon
    def &&&[A, B, C](f: T[B], g: T[C]): T[B /\ C] = L.product((f, g))

  trait SecondAssociativeDisj[T[_]] extends Associative.Proto[Second[T,*,*], \/, T]:
    given L: LaxSemigroupal[\/, Function, \/, T]
    def C: Subcat.Aux[Second[T,*,*], T] = summon
    def bifunctor: Endobifunctor[Second[T,*,*], \/] = summon
    def associate  [X: T, Y: T, Z: T]: T[X \/ (Y \/ Z)] = summon
    def diassociate[X: T, Y: T, Z: T]: T[(X \/ Y) \/ Z] = summon

  trait SecondCartesianDisj[T[_]] extends Cartesian.Proto[Second[T,*,*], \/, T, Void] with SecondAssociativeDisj[T]:
    given TU: T[Void]
    def idl[A: T]: T[A] = summon
    def idr[A: T]: T[A] = summon
    def coidl[A: T]: T[Void \/ A] = summon
    def coidr[A: T]: T[A \/ Void] = summon
    def fst[A: T, B: T]: T[A] = summon
    def snd[A: T, B: T]: T[B] = summon
    def diag[A: T]: T[A \/ A] = summon
    def braid[A: T, B: T]: T[B \/ A] = summon
    def &&&[A, B, C](f: T[B], g: T[C]): T[B \/ C] = L.product(-\/(f))

end EvidenceCatHelpers
