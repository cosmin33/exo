package io.cosmo.exo.evidence

import io.cosmo.exo._
import io.cosmo.exo.evidence.variance.IsCovariant
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite

class AsTest extends AnyFunSuite with Matchers {

  test("As resolution") {
    implicitly[Int <~< Int]
    implicitly[Int <~< AnyVal]

    implicitly[String <~< String]
    implicitly[String <~< AnyRef]
    implicitly[String <~< Any]

    implicitly[Nothing <~< Int]
    implicitly[Nothing <~< String]
    implicitly[Nothing <~< AnyRef]
    implicitly[Nothing <~< AnyVal]
    implicitly[Nothing <~< Any]

    implicitly[Null <~< String]
    implicitly[Null <~< AnyRef]
    implicitly[Null <~< Any]

    implicitly[Void <~< Int]
    implicitly[Void <~< Any {type A}]
    implicitly[Nothing <~< Any {type A}]
    implicitly[Void <~< Any {type TC[_]}]
    implicitly[Void <~< Any {type TC[_]}]

    implicitly[(String, Int) <~< (String, Any)]
    implicitly[(String, Int) <~< (Any, Any)]
    implicitly[(String, Int) <~< (AnyRef, AnyVal)]
    implicitly[(String, Int) <~< AnyRef]
    implicitly[(String, Int) <~< Any]
    implicitly[Null <~< (String, Int)]
    implicitly[Nothing <~< (String, Int)]

    trait Aa { type X }
    def f1(a: Aa): a.X <~< a.X = implicitly[a.X <~< a.X]

    trait F[L, H >: L] { type A >: L <: (H with B); type B >: L <: H }
    def g1[L, H >: L](a: F[L, H]): a.A <~< a.B = implicitly[a.A <~< a.B]
    def g2[L, H >: L](a: F[L, H]): a.A <~< a.B = implicitly[a.A <~< a.B]

    def h1[A, B >: A]: A <~< B = implicitly[A <~< B]
    def h2[A]: A <~< A         = implicitly[A <~< A]
  }

  test("As syntax") {
    import io.cosmo.exo.evidence.As.syntax._
    val ev1: Either[Int, String] <~< Either[AnyVal, AnyRef] =
      As.pair(implicitly[Int <~< AnyVal], implicitly[String <~< AnyRef]).liftCo[Either]

    def ev3[F[_]: IsCovariant](fa: F[Int]): Unit = {
      val (_, _) = (implicitly[Int <~< AnyVal].liftCvF[F], implicitly[Int <~< AnyVal].substCvF[F](fa): F[AnyVal])
    }

    val aa: Int <~< AnyVal = As.refl[Int]
    val bb: List[Int] <~< List[AnyVal] = aa.liftCvF[List]
    val cc: List[Int] <~< List[AnyVal] = aa.fix.liftCoF[List].loosen
    assert(bb == cc)
  }
}
