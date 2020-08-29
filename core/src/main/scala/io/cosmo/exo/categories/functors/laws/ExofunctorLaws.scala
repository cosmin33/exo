package io.cosmo.exo.categories.functors.laws

import cats.laws.IsEq
import cats.laws._
import io.cosmo.exo.categories.Subcat
import io.cosmo.exo.categories.functors.Exofunctor

trait ExofunctorLaws[==>[_,_], -->[_,_], F[_]] {
  def F: Exofunctor[==>, -->, F]

  def covariantIdentity[A, T1[_], T2[_]](implicit
    c1: Subcat.Aux[==>, T1], c2: Subcat.Aux[-->, T2], t1: T1[A], t2: T2[F[A]]
  ): IsEq[F[A] --> F[A]] =
    F.map(c1.id[A]) <-> c2.id[F[A]]

  def covariantComposition[A, B, C](f: A ==> B, g: B ==> C)(implicit
    c1: Subcat[==>], c2: Subcat[-->]
  ): IsEq[F[A] --> F[C]] =
    c2.andThen(F.map(f), F.map(g)) <-> F.map(c1.andThen(f, g))
}

object ExofunctorLaws {
  def apply[==>[_,_], -->[_,_], F[_]](implicit ev: Exofunctor[==>, -->, F]): ExofunctorLaws[==>, -->, F] =
    new ExofunctorLaws[==>, -->, F] { val F = ev }
}