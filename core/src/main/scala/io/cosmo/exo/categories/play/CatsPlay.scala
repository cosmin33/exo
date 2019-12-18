package io.cosmo.exo.categories.play

import cats.data.State
import cats.evidence.===
import cats.free.Free
import cats.free.Free._
import cats.{Monad, ~>}
import cats.syntax._
import io.cosmo.exo._
import io.cosmo.exo.syntax._

object CatsPlay {

  locally {
    // Recursion schemes
    sealed trait Expr
    case class Lit(i: Int)           extends Expr
    case class Add(l: Expr, r: Expr) extends Expr
    case class Mul(l: Expr, r: Expr) extends Expr

    // Final tagless
    trait ExprA[Z] {
      def lit(i: Int): Z
      def add(l: Z, r: Z): Z
      def mul(l: Z, r: Z): Z
    }
    // functions for iso
    def foldAlg[z](expr: Expr): ExprA[z] => z =
      (ea: ExprA[z]) => expr match {
          case Lit(i)    => ea.lit(i)
          case Add(l, r) => ea.add(foldAlg[z](l)(ea), foldAlg[z](r)(ea))
          case Mul(l, r) => ea.mul(foldAlg[z](l)(ea), foldAlg[z](r)(ea))
        }
    def reify: ExprA[Expr] = new ExprA[Expr] {
      override def lit(i: Int): Expr = Lit(i)
      override def add(l: Expr, r: Expr): Expr = Add(l, r)
      override def mul(l: Expr, r: Expr): Expr = Mul(l, r)
    }

    val iso: Expr <=> ∀[λ[z => ExprA[z] => z]] =
      Iso.unsafe(
        expr => ∀.of[λ[z => ExprA[z] => z]].from(foldAlg(expr)),
        _[Expr](reify)
      )

    // Free algebra:
    type Alg[G[_]] = ∀[λ[a => ExprA[a] => G[a]]]

    // Free monad
    locally {
      sealed trait ServiceF[+A]
      //case class Get1[A](key: A,           ev: A === Int) extends ServiceF[A]
      //case class Set1[A](key: A, value: A, ev: A === Int) extends ServiceF[A]
      //case class Get(key: Int            ) extends ServiceF[Int]
      //case class Set(key: Int, value: Int) extends ServiceF[Unit]
      //def get(key: Int):             Free[ServiceF, Int]  = liftF[ServiceF, Int](Get(key))
      //def set(key: Int, value: Int): Free[ServiceF, Unit] = liftF[ServiceF, Unit](Set(key, value))
      // gadt: ∀x(x = Int, Int) + (x = Unit, (Int, Int)) -> gx
      trait Algebra[G[_]] {
        def run[X](value: ServiceF[X]): G[X]
        // or
        def get(key: Int): G[Int]
        def set(key: Int, value: Int): G[Unit]
      }
      trait FreeA[Alg[_[_]], A] {
        def runFree[G[_]: Monad](alg: Alg[G]): G[A]
      }
      // ------so instead of:
      // def program: FreeA[ServiceAlg, Int] = ...
      // ------we might as well dispose of the FreeA type and simply write:
      // def program[G[_]: Monad](alg: ServiceAlg[G]): G[Int] = ...

//      val x = new (ServiceF ~> State[(Int, Int), *]) {
//        override def apply[A](value: ServiceF[A]): State[(Int, Int), A] =
//          value match {
//            case Get(key) =>
//                          for {
//                            state <- State.get[(Int, Int)]
//                            value = key match {
//                              case 0 => state._1
//                              case 1 => state._2
//                            }
//                          } yield value
//            case Set(key, value) =>
//                          for {
//                            state <- State.set((key, value))
//                          } yield ()
//          }
//      }
    }



    sealed trait KVStoreA[A]
    case class Put[T](key: String, value: T) extends KVStoreA[Unit]
    case class Get[T](key: String) extends KVStoreA[Option[T]]
    case class Delete(key: String) extends KVStoreA[Unit]

    type KVStore[A] = Free[KVStoreA, A]

    def put[T](key: String, value: T): KVStore[Unit] =
      liftF[KVStoreA, Unit](Put[T](key, value))

    // Get returns a T value.
    def get[T](key: String): KVStore[Option[T]] =
      liftF[KVStoreA, Option[T]](Get[T](key))

    // Delete returns nothing (i.e. Unit).
    def delete(key: String): KVStore[Unit] =
      liftF(Delete(key))

    // Update composes get and set, and returns nothing.
    def update[T](key: String, f: T => T): KVStore[Unit] =
      for {
        vMaybe <- get[T](key)
        _ <- vMaybe.map(v => put[T](key, f(v))).getOrElse(Free.pure(()))
      } yield ()

    def program: KVStore[Option[Int]] =
      for {
        _ <- put("wild-cats", 2)
        _ <- update[Int]("wild-cats", (_ + 12))
        _ <- put("tame-cats", 5)
        n <- get[Int]("wild-cats")
        _ <- delete("tame-cats")
      } yield n

    type KVStoreState[A] = State[Map[String, Any], A]
    val pureCompiler: KVStoreA ~> KVStoreState = new (KVStoreA ~> KVStoreState) {
      def apply[A](fa: KVStoreA[A]): KVStoreState[A] =
        fa match {
          case Put(key, value) => State.modify(_.updated(key, value))
          case Get(key) =>
            State.inspect(_.get(key).map(_.asInstanceOf[A]))
          case Delete(key) => State.modify(_ - key)
        }
    }

    val result: (Map[String, Any], Option[Int]) = program.foldMap(pureCompiler).run(Map.empty).value
    // result: (Map[String,Any], Option[Int]) = (Map(wild-cats -> 14),Some(14))

  }

  type ~:>[TC[_], F[_], G[_]] = ∀[λ[a => TC[a] => F[a] => G[a]]]

  // existentials via universals
  trait Forall1[F[_]] {
    def apply[A]: F[A]
  }
  type Consumer[F[_], R] = Forall1[λ[a => F[a] => R]]
  type Exists[F[_]] = Forall1[λ[r => Consumer[F, r] => r]]
  def existential[F[_], A](fa: F[A]): Exists[F] = ν[Exists[F]](_[A](fa))

  val list = existential(List("one", "two", "three"))
  val len = ν[Consumer[List, Int]](_.length)
  assert(list[Int](len) == 3)


}
