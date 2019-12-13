package io.cosmo.exo.evidence

import io.cosmo.exo._
import io.cosmo.exo.evidence.variance._

sealed abstract class As1[A, B] { ab =>
  type Upper >: A
  type Lower <: B with Upper

  def lower: A === Lower
  def upper: B === Upper

  def loosen: A <~< B =
    upper.flip.subst[A <~< *](
      lower.flip.subst[* <~< Upper](
        As.refl[Lower] : Lower <~< Upper))

  def substCt[F[-_]](fb: F[B]): F[A] = lower.flip.subst[F](upper.subst[F](fb) : F[Lower])
  def substCo[F[+_]](fa: F[A]): F[B] = upper.flip.subst[F](lower.subst[F](fa) : F[Upper])

  def coerce(a: A): B = substCo[λ[`+x` => x]](a)

  def liftCoF[F[_]: IsCovariant]: F[A] As1 F[B] = IsCovariant[F].apply(ab.loosen).fix
  def liftCtF[F[_]: IsContravariant]: F[B] As1 F[A] = IsContravariant[F].apply(ab.loosen).fix
  def substCoF[F[_]: IsCovariant](fa: F[A]): F[B] = liftCoF[F].coerce(fa)
  def substCtF[F[_]: IsContravariant](fb: F[B]): F[A] = liftCtF[F].coerce(fb)
}
object As1 {
  def apply[A, B](implicit ev: A As1 B): A As1 B = ev

  private[this] final case class Refl[A]() extends As1[A, A] {
    type Lower = A
    type Upper = A
    val lower, upper = Is.refl[A]
  }

  case class SingleOf[A, B, U <: {type Upper >: A; type Lower <: B with Upper}](
    widen: As1[A, B] {type Upper = U#Upper; type Lower = U#Lower}
  )
  object SingleOf {
    implicit def mkSingleOf[A, B, T <: As1[A, B] {type Upper; type Lower}](implicit
      as: As1[A, B]
    ): SingleOf[A, B, as.type] = SingleOf(as)
  }

  implicit def proposition[A, B]: Proposition[As1[A, B]] = Proposition[A <~< B].isomap(Iso.unsafeT(_.fix, _.loosen))

  def refl[A]: A As1 A = new Refl[A]()

  implicit def fix[A, B](implicit ab: A <~< B): A As1 B = ab.fix[A, B]

  def proved[A, B, B1 >: A, A1 <: B with B1](a: A === A1, b: B === B1): As1[A, B] = new As1[A, B] {
    type Upper = B1
    type Lower = A1
    def lower: A === Lower = a
    def upper: B === Upper = b
  }
}
