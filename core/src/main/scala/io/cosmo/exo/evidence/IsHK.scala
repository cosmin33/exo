package io.cosmo.exo.evidence

sealed abstract class IsHK[A1[_[_]], A2[_[_]]] { ab =>
  import IsHK._
  def subst[U[_[_[_]]]](fa: U[A1]): U[A2]

  final def coerce[F[_]](a: A1[F]): A2[F] = {
    type u[a[_[_]]] = a[F]
    subst[u](a)
  }

  def apply[F[_]](a: A1[F]): A2[F] = coerce[F](a)

  final def flip: A2 =≈= A1 = {
    type f[a[_[_]]] = a =≈= A1
    ab.subst[f](refl)
  }

}

object IsHK {

  private[this] final case class Refl[A[_[_]]]() extends IsHK[A, A] {
    def subst[U[_[_[_]]]](fa: U[A]): U[A] = fa
  }

  implicit def refl[A[_[_]]]: A =≈= A = new Refl[A]()

  def lower[U[_[_[_]]], A[_[_]], B[_[_]]](ab: A =≈= B): U[A] === U[B] = {
    type f[a[_[_]]] = U[A] === U[a]
    ab.subst[f](Is.refl)
  }

}
