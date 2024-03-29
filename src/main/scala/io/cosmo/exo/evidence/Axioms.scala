package io.cosmo.exo.evidence

import io.cosmo.exo.internal.Unsafe
import io.cosmo.exo.inhabitance.*
import io.cosmo.exo.*

/** Copied from alexknvl "Leibniz" library: https://github.com/alexknvl/leibniz */
object Axioms {
  def predefEq[A, B](ab: A =:= B): A === B = Unsafe.is[A, B]
  
  def predefConformity[A, B](eq: A <:< B): A <~< B = Unsafe.as[A, B]

  def isConsistency[A, B](ab: ¬¬[A === B]): A === B = Unsafe.is[A, B]

  def asConsistency[A, B](ab: ¬¬[A <~< B]): A <~< B = Unsafe.as[A, B]

  def isKConsistency[A[_], B[_]](ab: ((A =~= B) => Void) => Void): A =~= B = Unsafe.isK[A, B]

  def isK2Consistency[A[_,_], B[_,_]](ab: ((A =~~= B) => Void) => Void): A =~~= B = Unsafe.isK2[A, B]

  /** Subtyping is antisymmetric. */
  def bracket[A, B](f: A <~< B, g: B <~< A): A === B = Unsafe.is[A, B]

  /** ∀ a b x y. (f a = f b) ∧ ¬(a = b) => f x = f y */
  def phParametricity[F[_], A, B, X, Y](fab: F[A] === F[B], ab: (A === B) => Void)
  : F[X] === F[Y] = Unsafe.is[F[X], F[Y]]

  /** (a < b) ∧ (f a <= f b) => ∀ x y. (x <= y) => (f x <= f y) */
  def cvParametricity[F[_], A, B, X, Y](ab: (A === B) => Void, p: A <~< B, q: F[A] <~< F[B], r: X <~< Y)
  : F[X] <~< F[Y] = Unsafe.as[F[X], F[Y]]

  /** (a < b) ∧ (f b <= f a) => ∀ x y. (x <= y) => (f y <= f x) */
  def ctParametricity[F[_], A, B, X, Y](ab: (A === B) => Void, p: A <~< B, q: F[B] <~< F[A], r: X <~< Y)
  : F[Y] <~< F[X] = Unsafe.as[F[Y], F[X]]

  /** (a < b) ∧ (f a >< f b) => ∀ x y. (x < y) => (f x >< f y) */
  def invParametricity[F[_], A, B, X, Y](ab: A </< B, fab: F[A] >~< F[B], nxy: X =!= Y)
  : F[X] >~< F[Y] = Unsafe.incomparable[F[X], F[Y]]

  /** a ≸ b ⋀ f a ≠ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≸ f y */
  def parametricity1[F[_], A, B, X, Y](ab: A >~< B, nfxy: F[A] =!= F[B], nxy: X =!= Y)
  : F[X] >~< F[Y] = Unsafe.incomparable[F[X], F[Y]]

  /** (∀ x . f x = g x) => f = g */
  def tcExtensionality[F[_], G[_]]: TCExtensionality[F, G] = new TCExtensionality[F, G]
  final class TCExtensionality[F[_], G[_]](val b: Boolean = true) extends AnyVal {
    type T
    def apply(uv: F[T] === G[T]): F =~= G = Unsafe.isK[F, G]
    def applyT(f: [T] => () => (F[T] === G[T])): F =~= G = apply(f())
  }

  /** (∀ x,y . f x,y = g x,y) => f = g */
  def tcExtensionality2[F[_,_], G[_,_]]: TCExtensionality2[F, G] = new TCExtensionality2[F, G]
  final class TCExtensionality2[F[_,_], G[_,_]](val b: Boolean = true) extends AnyVal {
    type T1
    type T2
    def apply(uv: F[T1, T2] === G[T1, T2]): F =~~= G = Unsafe.isK2[F, G]
    def applyT(f: [T1, T2] => () => (F[T1, T2] === G[T1, T2])): F =~~= G = apply(f[T1, T2]())
  }

//  def fBounded[F[X <: F[X]], A <: F[A], B <: F[B], G[X <: F[X]]](eq: A === B, fa: G[A]): G[B] =
//    Unsafe.is[G[A], G[B]].apply(fa)
//
//  def bounded[L, H >: L, A >: L <: H, B >: L <: H, F[_ >: L <: H]](eq: A === B, fa: F[A]): F[B] =
//    Unsafe.is[F[A], F[B]].apply(fa)
//
//  /** Take two equal types `A === B` with different bounds `A >: LA <: HA`, `B >: LB <: HB`
//   * and find a new type `C === A === B` that is bounded by `C >: (LA | LB) <: (HA & HB)`.
//   * Due to Scala2's lack of unions, the signature is a bit uglier than it could be. */
//  def squash[
//    LA, HA >: LA, A >: LA <: HA,
//    LB >: LA <: HA, HB >: LB, B >: LB <: HB
//  ] (eq: A === B): Squash[LA, HA, A, LB, HB, B] =
//    Squash.refl[LA, HA, A].asInstanceOf[Squash[LA, HA, A, LB, HB, B]]
}
