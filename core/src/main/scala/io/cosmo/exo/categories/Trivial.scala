package io.cosmo.exo.categories

sealed trait Trivial

object Trivial {
  type T1[A] = Trivial
  type T2[F[_]] = Trivial
  type T3[A[_[_]]] = Trivial
  type T21[F[_], A] = Trivial
  type T11[A, B] = Trivial
  type T211[F[_], A, B] = Trivial
  type T111[A, B, C] = Trivial
  type T322[Alg[_[_]], F[_], G[_]] = Trivial

  implicit val trivialInstance: Trivial = new Trivial {}

}
