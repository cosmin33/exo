package io.cosmo.exo.evidence

import io.cosmo.exo._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
import shapeless.Refute

class IsTest extends AnyFunSuite with Matchers {

  test("Is test") {
    implicitly[Int === Int]
    implicitly[Nothing === Nothing]
    implicitly[Any === Any]

    trait Aa { type X }
    def f1(a: Aa): a.X === a.X = implicitly[a.X === a.X]
    def h1[A]: A === A = implicitly[A === A]
    def h2[A, B >: A <: A]: A === B = implicitly[A === B]
  }

  test("equality") {
    implicitly[Void === Nothing]

    object Test {
      type AnyLike >: Any
      implicitly[AnyLike === Any]
    }

    val i: 0 = 0
    val j: i.type = i
    implicitly[0 === i.type]
    implicitly[j.type === i.type]

    implicitly[Int === Int]
    implicitly[Nothing === Nothing]
    implicitly[Any === Any]
    implicitly[0 === 0]
    implicitly["" === ""]

    implicitly[Refute[1 === 0]]
    implicitly[Refute[Null === Void]]
    implicitly[Refute[Any === Void]]
    implicitly[Refute[AnyRef === Any]]

    type g[xx] = Unit
    type h[xx] = g[g[xx]]
    type f[xx] = List[h[xx]]
    implicitly[f[Int] === List[Unit]]
  }

  test("liskov simple") {
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
    implicitly[Nothing <~< Any {type A}]
    implicitly[Nothing <~< Any {type TC[_]}]

    implicitly[Null <~< String]
    implicitly[Null <~< AnyRef]
    implicitly[Null <~< Any]

    implicitly[(String, Int) <~< (String, Any)]
    implicitly[(String, Int) <~< (Any, Any)]
    implicitly[(String, Int) <~< (AnyRef, AnyVal)]
    implicitly[(String, Int) <~< AnyRef]
    implicitly[(String, Int) <~< Any]
    implicitly[Null <~< (String, Int)]
    implicitly[Nothing <~< (String, Int)]

    implicitly[Int As1 AnyVal]
  }


  test("hk equality") {
    type Id[x] = x
    implicitly[List =~= List]
    implicitly[Id =~= Id]
    implicitly[Either[Int, ?] =~= Either[Int, ?]]
    implicitly[(Int => ?) =~= (Int => ?)]


    type Li[a] = List[a]
    implicitly[List =~= List]
    implicitly[Li =~= List]
    implicitly[Refute[Option =~= List]]

    implicitly[(* => Int) =~= (* => Int)]
    implicitly[Refute[(* => Int) =~= (Int => *)]]
  }

  test("complex === and <~<") {
    trait Aa { type X }
    def f1(a: Aa): a.X === a.X = implicitly[Is[a.X, a.X]]
    def f2(a: Aa): a.X <~< a.X = implicitly[As[a.X, a.X]]
    def f3(a: Aa): As1[a.X, a.X] = implicitly[As1[a.X, a.X]]

    trait F[L, H >: L] { type A >: L <: (H with B); type B >: L <: H }
    def g1[L, H >: L](a: F[L, H]): Is[a.A, a.A] = implicitly[Is[a.A, a.A]]
    def g2[L, H >: L](a: F[L, H]): As[a.A, a.B] = implicitly[As[a.A, a.B]]
    def g3[L, H >: L](a: F[L, H]): As[a.A, a.B] = implicitly[As[a.A, a.B]]

    def h1[A, B >: A]: As[A, B] = implicitly[As[A, B]]
    def h2[A]: Is[A, A] = implicitly[Is[A, A]]
    def h3[A]: As[A, A] = implicitly[As[A, A]]
  }


}
