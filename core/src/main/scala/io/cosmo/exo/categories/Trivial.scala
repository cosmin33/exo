package io.cosmo.exo.categories

import io.cosmo.exo.{∀, ∀~, ∀∀}

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
  implicit def faTrivial[F[_]]: ∀[λ[a => T1[F[a]]]] = ∀.of[λ[a => T1[F[a]]]].from(trivialInstance)
  implicit def faTrivial2[F[_,_]]: ∀∀[λ[(a,b) => T1[F[a, b]]]] = ∀∀.of[λ[(a, b) => T1[F[a, b]]]].from(trivialInstance)
  implicit def faTrivialK[A[_[_]]]: ∀~[λ[f[_] => T1[A[f]]]] = ∀~.of[λ[f[_] => T1[A[f]]]].from(trivialInstance)
}
