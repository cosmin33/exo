package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.Trivial.{T1 => Trivial}
import cats._
import io.cosmo.exo._

trait Exomonad[->[_,_], I[_], F[_]] extends Endofunctor.ProtoA[->, F] {
  def I: Endofunctor.Aux[->, TC1, I]
  def pure[A]: I[A] -> F[A]
  def bind[A, B](f: I[A] -> F[B]): F[A] -> F[B]
}

object Exomonad {
  type Aux[->:[_, _], ->#[_], I[_], F[_]] = Exomonad[->:, I, F] with Endofunctor.Proto[->:, ->#, F]
  type AuxT[->:[_, _], I[_], F[_]] = Aux[->:, Trivial, I, F]
  type AuxF[I[_], F[_]] = Aux[Function1, Trivial, I, F]

//  implicit def monad2monad[F[_]](implicit F: Exomonad.AuxF[Id, F]): cats.Monad[F] =
//    new cats.Monad[F] {
//      override def pure[A](x: A): F[A] = F.pure.apply(x)
//      override def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = F.bind[A, B](f).apply(fa)
//      override def tailRecM[A, B](a: A)(f: A => F[Either[A, B]]): F[B] = ???
//    }
//
//  def monad2monadFlip[F[_]](implicit M: cats.Monad[F]): Exomonad.AuxF[Id, F] =
//    new Exomonad.AuxF[Id, F] {
//      override def I: Endofunctor.Aux[Function1, Trivial, Id] = implicitly
//      override def C: Category.AuxT[Function] = implicitly
//      override def pure[A]: A --> F[A] = M.pure
//      override def bind[A, B](f: Id[A] --> F[B]): F[A] --> F[B] = fa => M.flatMap(fa)(f)
//      override def map[A, B](f: A |=> B): F[A] --> F[B] = fa => M.map(fa)(f)
//    }
//
//  implicit def isoMonad2Exomonad[F[_]]: cats.Monad[F] => cats.Monad[F] <=> Exomonad.AuxF[Id, F] =
//    Iso.unsafeT(
//      to   = (M: cats.Monad[F]) =>
//        new Exomonad.AuxF[Id, F] {
//          override def I: Endofunctor.AuxF[Id] = implicitly
//          override def C: CategoryClass.Aux[-->, Trivial] = implicitly
//          //override def C: Category.AuxT[Function] = implicitly
//          override def pure[A]: A --> F[A] = M.pure
//          override def bind[A, B](f: Id[A] --> F[B]): F[A] --> F[B] = fa => M.flatMap(fa)(f)
//          override def map[A, B](f: A |=> B): F[A] --> F[B] = fa => M.map(fa)(f)
//        }: Exomonad.AuxF[Id, F],
//      from = (F: Exomonad.AuxF[Id, F]) =>
//      new cats.Monad[F] {
//        override def pure[A](x: A): F[A] = F.pure.apply(x)
//        override def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = F.bind[A, B](f).apply(fa)
//        override def tailRecM[A, B](a: A)(f: A => F[Either[A, B]]): F[B] = ???
//      }: cats.Monad[F]
//    )


//  def xxMonad: Exomonad.Aux[Function1, Trivial, Id, List] =
//    new Exomonad.Aux[Function1, Trivial, Id, List] {
//      override def I: Endofunctor.Aux[Function1, Trivial, Id] = implicitly[Endofunctor.Aux[Function1, Trivial, Id]]
//      override def C: Category.Aux[Function1, Trivial] = implicitly
//      override def D: Category.Aux[Function1, Trivial] = implicitly
//      override def pure[A]: A => List[A] = List(_)
//      override def bind[A, B](f: A => List[B]): List[A] => List[B] = (l: List[A]) => l.flatMap(f)
//      override def map[A, B](f: A => B): List[A] => List[B] = (l: List[A]) => l.map(f)
//    }

}