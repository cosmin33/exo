package io.cosmo.exo.evidence

import io.cosmo.exo._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
import shapeless.Refute

class IsInjectiveTests extends AnyFunSuite with Matchers {

  trait Atrait
  trait AAtrait extends Atrait

  test("proposition") {
    implicitly[Proposition[Proposition[0]]]
    implicitly[Proposition[0 === 1]]
    implicitly[Proposition[Inhabited[0]]]
    implicitly[Proposition[Inhabited[Void]]]
  }

  test("singleton of") {
    SingletonOf[0, 0]
    SingletonOf[0, Int]
    SingletonOf[0, AnyVal]
    SingletonOf[0, Any]
    SingletonOf[None.type, None.type]
    SingletonOf[None.type, Option[Int]]
    SingletonOf[None.type, Option[String]]

    implicitly[ValueOf[0]]
    implicitly[ValueOf["blah"]]
    val x: Unit = implicitly[ValueOf[Unit]]
    implicitly[ValueOf[5.7546]]


  }
  test("inequality") {
    val int0 = 0
    val long0 = 0



    implicitly[0 =!= 1]
    implicitly[0 =!= 0L]
    implicitly[0 =!= "a"]
    implicitly[List[0] =!= List[1]]
    implicitly[List[1] =!= List[1L]]
    implicitly[Void =!= Any]
    implicitly[Void =!= Null]
    implicitly[Void =!= AnyRef]
    implicitly[Void =!= AnyVal]
    implicitly[Void =!= List[Int]]
    implicitly[Any =!= AnyRef]
    implicitly[Any =!= AnyVal]
    implicitly[AnyVal =!= AnyRef]
    implicitly[Int =!= Long]
    implicitly[Int =!= 0]

    implicitly[None.type =!= 0]

    implicitly[Refute[0 =!= 0]]
    implicitly[Refute[(Int with String) =!= (String with Int)]]
    implicitly[Refute[Int =!= Int]]

    type g[xx] = Unit
    type h[xx] = g[g[xx]]
    type f[xx] = List[h[xx]]
    implicitly[Refute[List[Unit] =!= f[Int]]]
    //implicitly[Int =!= Int with Long]
  }

//  test("concrete types") {
//    TypeId[0]
//    TypeId[Nothing]
//    TypeId[Void]
//    TypeId[Int]
//    TypeId[String]
//    TypeId[List[Option[Int]]]
//    TypeId["abc"]
//    TypeId[List["abc"]]
//    TypeId[List[Array[Seq[Option[1]]]]]
//  }

  test("strong inequality") {
    val int0 = 0
    val long0 = 0
//    Apart[0, 1]
//    Apart[0, 0L]
//    Apart[0, "a"]
//    Apart[List[0], List[1]]
//    Apart[List[1], List[1L]]
//    Apart[Void, Any]
//    Apart[Void, Null]
//    Apart[Void, AnyRef]
//    Apart[Void, AnyVal]
//    Apart[Any, AnyRef]
//    Apart[Any, AnyVal]
//    Apart[AnyVal, AnyRef]
//    Apart[Int, Long]
//    Apart[Int, 0]

    // Apart[None.type, 0]

    // implicitly[Int =!= Int with Long]
  }

  test("injectivity") {
    // Constant type lambdas are not injective.
    implicitly[Refute[IsInjective[λ[x => List[Int]]]]]
    implicitly[Refute[IsInjective[λ[x => Unit]]]]

    // Identity is injective.
    IsInjective[λ[x => x]]
    IsInjective[({type L[x] = x})#L]

    implicitly[List[Void] =!= List[Any]]

    { type f[x] = x; IsInjective[f] }

    { type f[+x] = x; IsInjective[f] }

    // (Class) type constructors are injective.
    IsInjective[Option]

    // Aliases to (class) type constructors are injective.
    IsInjective[List]

    IsInjective[Either[Int, ?]]

    // A more complex test.
    {
      type g[x, y] = List[(x, y)]
      type f[x] = g[x, x]
      implicitly[f[Int] === List[(Int, Int)]]
      IsInjective[f]
    }

    {
      type k[xx] = Unit
      type f[xx] = List[k[xx]]
      implicitly[f[Int] === List[Unit]]
      implicitly[Refute[IsInjective[f]]]
    }

    {
      type k[xx] = Unit
      type h[xx] = k[k[xx]]
      type g[xx, y] = List[h[xx]]
      type f[xx] = g[xx, xx]
      implicitly[f[Int] === List[Unit]]
      implicitly[Refute[IsInjective[f]]]
    }

  }

}
