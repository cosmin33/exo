package io.cosmo.exo.categories.functors

import cats._
import io.cosmo.exo._
import io.cosmo.exo.categories.{Endofunctor, Subcat, Trivial}

import scala.annotation.tailrec

trait Exomonad[-->[_,_], TC[_], F[_]] extends Endofunctor[-->, F] {
  def pure[A: TC]: A --> F[A]
  def bind[A, B](f: A --> F[B]): F[A] --> F[B]
}

object Exomonad {

  type ExoM[->[_,_], TC[_], F[_]] = Exo[λ[(a,b) => a -> F[b]], ->, F] with Subcat.Aux[λ[(a,b) => a -> F[b]], TC]
  def testExoM[F[_]](implicit M: Monad[F]): ExoM[* => *, Trivial.T1, F] =
    new Exofunctor[λ[(a,b) => a => F[b]], * => *, F] with Subcat[λ[(a,b) => a => F[b]]] {
      type TC[a] = Trivial.T1[a]
      def id[A](implicit tc: TC[A]): A => F[A] = M.pure
      def map[A, B](f: A => F[B]): F[A] => F[B] = M.flatMap(_)(f)
      def andThen[A, B, C](ab: A => F[B], bc: B => F[C]): A => F[C] = a => M.flatMap(ab(a))(bc)
    }

  implicit def isoMonad2Exomonad[F[_]]: Monad[F] <=> Exomonad[* => *, Id, F] =
    Iso.unsafe(
      (M: cats.Monad[F]) =>
        new Exomonad[* => *, Id, F] {
          def pure[A: Id]: A => F[A] = M.pure
          def bind[A, B](f: A => F[B]) = M.flatMap(_)(f)
          def map[A, B](f:  A => B) = M.map(_)(f)
        },
      (F: Exomonad[* => *, Id, F]) =>
        new Monad[F] {
          def pure[A](x: A): F[A] = F.pure(x).apply(x)
          def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = F.bind[A, B](f).apply(fa)
          // should be: @tailrec
          def tailRecM[A, B](a: A)(f: A => F[Either[A, B]]): F[B] = flatMap(f(a))(_.fold(tailRecM(_)(f), pure))
        }
    )
}