package io.github.cosmin33.exo.evidence

import zio.test.*
import io.github.cosmin33.exo.*
import io.github.cosmin33.exo.categories.{Distributive, *}

object Blah extends ZIOSpecDefault {

  val head: List ~> Option = ~>([A] => (l: List[A]) => l.headOption)
  
  def spec = suite("Disjunction")(
    test("toEither") {
      assertTrue(head.run(List(1, 2, 3)).contains(1)) &&
        assertTrue(head.apply(List(1, 2, 3)).contains(1))
    }
  )


}
