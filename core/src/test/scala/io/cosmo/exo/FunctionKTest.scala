package io.cosmo.exo

import zio.test._

object FunctionKTest extends ZIOSpecDefault {

  val head: List ~> Option = [A] => (l: List[A]) => l.headOption

  def spec = suite("Disjunction")(
    test("toEither") {
      assertTrue(head.exec(List(1,2,3)) == Some(1))
    }
  )
}
