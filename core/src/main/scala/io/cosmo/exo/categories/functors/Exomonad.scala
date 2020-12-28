package io.cosmo.exo.categories.functors

import cats._
import io.cosmo.exo._
import io.cosmo.exo.categories.Endofunctor

import scala.annotation.tailrec

trait Exomonad[->[_,_], I[_], F[_]] extends Endofunctor[->, F] {
  def I: Endofunctor[->, I]
  def pure[A]: I[A] -> F[A]
  def bind[A, B](f: I[A] -> F[B]): F[A] -> F[B]
}

object Exomonad {

  implicit def isoMonad2Exomonad[F[_]]: Monad[F] <=> Exomonad[* => *, Id, F] =
    Iso.unsafe(
      (M: cats.Monad[F]) =>
        new Exomonad[* => *, Id, F] {
          override def I: Endofunctor[* => *, Id] = implicitly
          def pure[A]: A => F[A] = M.pure
          def bind[A, B](f: A => F[B]) = M.flatMap(_)(f)
          def map[A, B](f:  A => B) = M.map(_)(f)
        },
      (F: Exomonad[* => *, Id, F]) =>
        new Monad[F] {
          def pure[A](x: A): F[A] = F.pure.apply(x)
          def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = F.bind[A, B](f).apply(fa)
          //@tailrec
          def tailRecM[A, B](a: A)(f: A => F[Either[A, B]]): F[B] = flatMap(f(a))(e => e.fold(tailRecM(_)(f), pure))
        }
    )

}