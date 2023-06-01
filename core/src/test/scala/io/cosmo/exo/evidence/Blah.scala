package io.cosmo.exo.evidence

import zio.test.*
import io.cosmo.exo.*
import io.cosmo.exo.categories.{Distributive, *}

object Blah extends ZIOSpecDefault {

  val head: List ~> Option = [A] => (l: List[A]) => l.headOption
  
  def spec = suite("Disjunction")(
    test("toEither") {
      assertTrue(head.exec(List(1,2,3)) == Some(1)) &&
        assertTrue(head.forall.apply(List(1,2,3)) == Some(1))
    }
  )


}
