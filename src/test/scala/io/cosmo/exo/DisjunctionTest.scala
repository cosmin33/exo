package io.cosmo.exo

import zio.test._

object DisjunctionTest extends ZIOSpecDefault {
  val x1: \/[Int, String] = \/-("x")
  val x2: \/[Int, String] = -\/(1)
  val e1: Either[Int, String] = x1.toEither

  def spec = suite("Disjunction")(
    test("summons work correctly") {
      given Int = 1
      given String = "x"

      assertTrue(summon[Int \/ String] == -\/(1)) &&
        assertTrue(summon[Int \/ Long] == -\/(1)) &&
        assertTrue(summon[String \/ Int] == -\/("x"))
    }
  )
}
