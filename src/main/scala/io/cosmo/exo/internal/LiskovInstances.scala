package io.cosmo.exo.internal

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.{Endobifunctor, *}

class LiskovInstances {
  given liskovCartesian: Cartesian.Aux[<~<, &, Trivial, Any] = LiskovCartesian
  given liskovCocartesian: Cocartesian.Aux[<~<, |, Trivial, Void] =
    Dual.leibniz.subst[[f[_,_]] =>> Cartesian.Aux[f, |, Trivial, Void]](LiskovCocartesian)
  given liskovDistributive: Distributive.Aux[<~<, Trivial, &, Any, |, Void] = LiskovDistributive
  given liskovInitial: Initial.Aux[<~<, Trivial, Any] = new Initial.Proto[<~<, Trivial, Any] {
    def TC: Trivial[Any] = Trivial[Any]
    def subcat: Subcat.Aux[<~<, Trivial] = liskovDistributive
    def initiate[A: Trivial]: Any <~< A = Unsafe.as
  }
  given liskovTerminal: Terminal.Aux[<~<, Trivial, Void] = new Terminal.Proto[<~<, Trivial, Void] {
    def TC: Trivial[Void] = Trivial[Void]
    def subcat: Subcat.Aux[Dual[<~<,*,*], Trivial] = summon
    def terminate[A: Trivial]: A <~< Void = Unsafe.as
  }
}

object LiskovDistributive extends Distributive[<~<, &, |] {
  type TC[a] = Trivial[a]
  type ProductId = Any
  type SumId = Void
  def id[A: TC]: A <~< A = As.refl
  def andThen[A, B, C](ab: A <~< B, bc: B <~< C): A <~< C = ab.andThen(bc)
  def cartesian: Cartesian.Aux[<~<, [a,b] =>> a & b, Trivial, Any] = LiskovCartesian
  def cocartesian: Cocartesian.Aux[<~<, |, Trivial, Void] = <~<.liskovCocartesian
  def distribute[A: TC, B: TC, C: TC]: (A & (B | C)) <~< ((A & B) | (A & C)) = summon
}

object LiskovCartesian extends Cartesian[<~<, &] {
  type TC[a] = Trivial[a]
  type Id = Any
  def C: Subcategory.Aux[<~<, TC] = LiskovDistributive
  def braid[A: TC, B: TC]: (A & B) <~< (B & A) = summon
  def fst[A: TC, B: TC]: (A & B) <~< A = summon
  def snd[A: TC, B: TC]: (A & B) <~< B = summon
  def diag[A: TC]: A <~< (A & A) = summon
  def &&&[A, B, C](f: A <~< B, g: A <~< C): A <~< (B & C) = Unsafe.as
  def idl[A: TC]: (Any & A) <~< A = summon
  def coidl[A: TC]: A <~< (Any & A) = summon
  def idr[A: TC]: (A & Any) <~< A = summon
  def coidr[A: TC]: A <~< (A & Any) = summon
  def bifunctor: Endobifunctor[<~<, [a, b] =>> a & b] = new Endobifunctor[<~<, [a, b] =>> a & b]:
    def bimap[A, B, C, D](f: A <~< B, g: C <~< D): (A & C) <~< (B & D) = Unsafe.as
  def associate  [X: TC, Y: TC, Z: TC]: ((X & Y) & Z) <~< (X & (Y & Z)) = summon
  def diassociate[X: TC, Y: TC, Z: TC]: (X & (Y & Z)) <~< ((X & Y) & Z) = summon
}

object LiskovCocartesian extends Cartesian[Opp[<~<]#l, |] {
  type TC[a] = Trivial[a]
  type Id = Void
  def C: Subcategory.Aux[Opp[<~<]#l, TC] = Semicategory.oppSubcat(using LiskovDistributive)
  def braid[A: TC, B: TC]: (B | A) <~< (A | B) = summon
  def fst[A: TC, B: TC]: A <~< (A | B) = summon
  def snd[A: TC, B: TC]: B <~< (A | B) = summon
  def diag[A: TC]: (A | A) <~< A = summon
  def &&&[A, B, C](f: B <~< A, g: C <~< A): (B | C) <~< A = Unsafe.as
  def idl[A: TC]: A <~< (Void | A) = summon
  def coidl[A: TC]: (Void | A) <~< A = summon
  def idr[A: TC]: A <~< (A | Void) = summon
  def coidr[A: TC]: (A | Void) <~< A = summon
  def bifunctor: Endobifunctor[Opp[<~<]#l, [a, b] =>> a | b] = new Endobifunctor[Opp[<~<]#l, [a, b] =>> a | b]:
    def bimap[A, B, C, D](f: B <~< A, g: D <~< C): (B | D) <~< (A | C) = Unsafe.as
  def associate  [X: TC, Y: TC, Z: TC]: (X | (Y | Z)) <~< ((X | Y) | Z) = summon
  def diassociate[X: TC, Y: TC, Z: TC]: ((X | Y) | Z) <~< (X | (Y | Z)) = summon
}
