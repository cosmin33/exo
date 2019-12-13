package io.cosmo.exo

import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite

class TestTemp extends AnyFunSuite with Matchers {

    test("") {

      import cats.arrow._
      import cats.implicits._
      import cats.data.Kleisli

      def combine[->[_, _]: Arrow, A, B, C](fab: A -> B, fac: A -> C): A -> (B, C) =
        Arrow[->].lift((a: A) => (a, a)) >>> fab *** fac

      val mean: List[Int] => Double =
        combine((_: List[Int]).sum, (_: List[Int]).size) >>> {case (x, y) => x.toDouble / y}

      val variance: List[Int] => Double =
      // Variance is mean of square minus square of mean
        combine(((_: List[Int]).map(x => x * x)) >>> mean, mean) >>> {case (x, y) => x - y * y}

      val meanAndVar: List[Int] => (Double, Double) = combine(mean, variance)
      meanAndVar(List(1, 2, 3, 4))
      // res0: (Double, Double) = (2.5,1.25)

      val mean2: List[Int] => Double = xs => xs.sum.toDouble / xs.size

      val variance2: List[Int] => Double = xs => mean2(xs.map(x => x * x)) - scala.math.pow(mean2(xs), 2.0)

      val headK: Kleisli[Option, List[Int], Int] = Kleisli((_: List[Int]).headOption)
      val lastK: Kleisli[Option, List[Int], Int] = Kleisli((_: List[Int]).lastOption)

      val headPlusLast = combine(headK, lastK) >>> Arrow[Kleisli[Option, *, *]].lift(((_: Int) + (_: Int)).tupled)

      headPlusLast.run(List(2, 3, 5, 8))
      // res1: Option[Int] = Some(10)

      headPlusLast.run(Nil)
      // res2: Option[Int] = None

      case class FancyFunction[A, B](run: A => (FancyFunction[A, B], B))

      def runList[A, B](ff: FancyFunction[A, B], as: List[A]): List[B] = as match {
        case h :: t =>
          val (ff2, b) = ff.run(h)
          b :: runList(ff2, t)
        case _ => List()
      }

      implicit val arrowInstance: Arrow[FancyFunction] = new Arrow[FancyFunction] {

        override def lift[A, B](f: A => B): FancyFunction[A, B] = FancyFunction(lift(f) -> f(_))

        override def first[A, B, C](fa: FancyFunction[A, B]): FancyFunction[(A, C), (B, C)] = FancyFunction {case (a, c) =>
          val (fa2, b) = fa.run(a)
          (first(fa2), (b, c))
        }

        override def id[A]: FancyFunction[A, A] = FancyFunction(id -> _)

        override def compose[A, B, C](f: FancyFunction[B, C], g: FancyFunction[A, B]): FancyFunction[A, C] = FancyFunction {a =>
          val (gg, b) = g.run(a)
          val (ff, c) = f.run(b)
          (compose(ff, gg), c)
        }
      }

      def accum[A, B](b: B)(f: (A, B) => B): FancyFunction[A, B] = FancyFunction {a =>
        val b2 = f(a, b)
        (accum(b2)(f), b2)
      }

      runList(accum[Int, Int](0)(_ + _), List(6, 5, 4, 3, 2, 1))
      // res3: List[Int] = List(6, 11, 15, 18, 20, 21)

      import cats.kernel.Monoid

      def sum[A: Monoid]: FancyFunction[A, A] = accum(Monoid[A].empty)(_ |+| _)
      def count[A]: FancyFunction[A, Int] = Arrow[FancyFunction].lift((_: A) => 1) >>> sum

      def avg: FancyFunction[Int, Double] =
        combine(sum[Int], count[Int]) >>> Arrow[FancyFunction].lift{case (x, y) => x.toDouble / y}

      runList(avg, List(1, 10, 100, 1000))
      // res4: List[Double] = List(1.0, 5.5, 37.0, 277.75)
    }

}
