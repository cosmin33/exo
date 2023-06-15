package io.cosmo.exo

import zio.test._

object FunctionKTest extends ZIOSpecDefault {

  val head: List ~> Option = ~>([A] => (l: List[A]) => l.headOption)
  val twice: Option ~> List = ~>([A] => (o: Option[A]) => o.toList ++ o.toList)
  
  def spec = suite("~>")(
    test("run correctly") {
      assertTrue(head.run(List(1, 2, 3)).contains(1)) &&
        assertTrue(twice.run(Some(1)) == List(1,1))
    }
  )
}
