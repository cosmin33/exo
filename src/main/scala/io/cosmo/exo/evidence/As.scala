package io.cosmo.exo.evidence

import io.cosmo.exo.*
import io.cosmo.exo.inhabitance.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.*
import io.cosmo.exo.variance.*

sealed abstract class As[-A, +B] private[As]() { ab =>
  import As._

  def fix[A1 <: A, B1 >: B]: As1[A1, B1]

  def substCv[F[+_]](fa: F[A]): F[B] = fix[A, B].substCo[F](fa)
//  def substCv[F[+_]](fa: F[A]): F[B] = fix[A, B].substCo[F](fa)

  def substCt[F[-_]](fb: F[B]): F[A] = fix[A, B].substCt[F](fb)

  final def apply(a: A): B = coerce(a)

  final def andThen[C](bc: B <~< C): A <~< C = {
    type f[+x] = A <~< x
    bc.substCv[f](this)
  }

  final def compose[Z](za: Z <~< A): Z <~< B = za.andThen(ab)

  final def coerce(a: A): B = substCv[[x] =>> x](a)

  final def liftCo[F[+_]]: F[A] <~< F[B] = {
    type f[+x] = F[A] <~< F[x]
    substCv[f](refl[F[A]])
  }

  final def liftCt[F[-_]]: F[B] <~< F[A] = {
    type f[+x] = F[x] <~< F[A]
    substCv[f](refl)
  }

  def onF[X](fa: X => A): X => B = substCv[X => +*](fa)

  final def toPredef: A <:< B = {
    type f[+a] = A <:< a
    substCv[f](implicitly[A <:< A])
  }

  /** a ≤ b ⟷ a < b \/ a ~ b */
  def decompose[AA <: A, BB >: B]: ¬¬[(AA </< BB) Either (AA === BB)] =
    Inhabited.lem[AA === BB].map {
      _.fold(
        notEqual => Left(StrictAs.witness[AA, BB](WeakApart.witness(notEqual), ab)),
        equal => Right(equal)
      )
    }

}

object As extends LiskovInstances {
  def apply[A, B](implicit ev: A <~< B): A <~< B = ev

  private[this] val forall: ∀[[a] =>> a <~< a] = ∀.of[[a] =>> a <~< a].fromH(
    [A] => () => new (A <~< A) { def fix[A1 <: A, B1 >: A] = As1.proved(Is.refl[A1], Is.refl[B1])}
  )

  def refl[A]: A <~< A = forall[A]

  given reify[A, B >: A]: (A <~< B) = refl[A]

  given proposition[A, B]: Proposition[A <~< B] = new Proposition[A <~< B]:
    def proved(using i: ¬¬[A <~< B]): A <~< B = Axioms.asConsistency[A, B](i)

  /** Antisymmetric */
  def bracket[A, B](f: A <~< B, g: B <~< A): A === B = Axioms.bracket[A, B](f, g)

  def pair[A1, B1, A2, B2] (eq1: A1 <~< B1, eq2: A2 <~< B2): Pair[A1, B1, A2, B2] = Pair(eq1, eq2)

  final case class Pair[A1, B1, A2, B2] (eq1: A1 <~< B1, eq2: A2 <~< B2) {
    def liftCo[F[+_, +_]]: F[A1, A2] <~< F[B1, B2] = {
      type f1[+a1] = F[A1, A2] <~< F[a1, A2]
      type f2[+a2] = F[A1, A2] <~< F[B1, a2]
      eq2.substCv[f2](eq1.substCv[f1](refl[F[A1, A2]]))
    }
    def liftCt[F[-_, -_]]: F[B1, B2] <~< F[A1, A2] = {
      type f1[+a1] = F[a1, A2] <~< F[A1, A2]
      type f2[+a2] = F[B1, a2] <~< F[A1, A2]
      eq2.substCv[f2](eq1.substCv[f1](refl[F[A1, A2]]))
    }
    def substCo[F[+_, +_]](value: F[A1, A2]): F[B1, B2] =
      liftCo[F].apply(value)
    def substCt[F[-_, -_]](value: F[B1, B2]): F[A1, A2] =
      liftCt[F].apply(value)
  }

  def fromPredef[A, B](ev: A <:< B): A <~< B = Axioms.predefConformity[A, B](ev)

  val bottomTop: Void <~< Any = reify[Void, Any]

  given asIsCovariant[A]: IsCovariant[[x] =>> A <~< x] = IsCovariant.reify[[x] =>> A <~< x]

  given asIsContravariant[A]: IsContravariant[[x] =>> x <~< A] = IsContravariant.reify[[x] =>> x <~< A]

  given liskovCovFunctor[F[_]](using ec: IsCovariant[F] \/ IsConstant[F]): Exo[<~<, <~<, F] =
    Exo.unsafe[<~<, <~<, F]([A, B] => (f: A <~< B) => ec.fold(cv => cv(using f), const => const[A, B].toAs))

  given liskovConFunctor[F[_]](using ec: IsContravariant[F] \/ IsConstant[F]): Exofunctor[Opp[<~<]#l, <~<, F] =
    Exo.unsafe[Opp[<~<]#l, <~<, F]([A, B] => (f: B <~< A) => ec.fold(cn => cn(using f), const => const[A, B].toAs))

}
