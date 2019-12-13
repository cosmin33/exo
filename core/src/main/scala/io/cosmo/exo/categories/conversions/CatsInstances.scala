package io.cosmo.exo.categories.conversions

import cats._
import io.cosmo.exo.<=>
import io.cosmo.exo.categories.functors._
import shapeless.LowPriority

object CatsInstances extends CatsInstances01 {
  implicit def exofunctor3invariant[F[_]](implicit lp: LowPriority, F: Exofunctor.InvF[F]): Invariant[F] = Exofunctor.isoInvariant[F].to(F)
  implicit def exofunctor2invariant[F[_]](implicit F: Invariant[F]): Exofunctor.InvF[F] = Exofunctor.isoInvariant[F].from(F)
}

trait CatsInstances01 {
  implicit def endofunctor2functor[F[_]](implicit lp: LowPriority, F: Endofunctor.CovF[F]): Functor[F] = Exofunctor.isoCovariant[F].to(F)
  implicit def endofunctor3functor[F[_]](implicit F: Functor[F]): Endofunctor.CovF[F] = Exofunctor.isoCovariant[F].from(F)

  implicit def exofunctor2contra[F[_]](implicit lp: LowPriority, F: Exofunctor.ConF[F]): Contravariant[F] = Exofunctor.isoContravariant[F].to(F)
  implicit def exofunctor3contra[F[_]](implicit F: Contravariant[F]): Exofunctor.ConF[F] = Exofunctor.isoContravariant[F].from(F)
}