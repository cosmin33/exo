package io.cosmo.exo

import zio.test.*
import io.cosmo.exo.syntax._
import io.cosmo.exo.evidence._
import io.cosmo.exo.categories._

object SyntaxTest extends ZIOSpecDefault {
  def spec = suite("syntax")(
    test("curry") {
      val fn: (Int, Int) => String = (a, b) => "(" + a.toString + ", " + b.toString + ")"
      summon[Ccc[Function, Tuple2, Function]]
//      val fn1 = fn.curry
      assertTrue(fn(1, 2) == "(1, 2)")
    },
    test("isoTo") {
      assertTrue(/\(1, "a").isoTo[(Int, String)] == (1, "a"))
    },
    test("left, right") {
      assertTrue(1.left[String] == Left(1)) &&
      assertTrue(1.right[String] == Right(1))
    },
    test(">>>, <<<") {
      val f: Int => String = _.toString
      val g: String => Boolean = _.length > 1
      assertTrue((f >>> g)(1) == false) &&
      assertTrue((g <<< f)(1) == false)
    },
    test("flipped") {
      assertTrue(===[1, 1].flipped.subst(List(1)) == List[1](1))
    }
  )

}