package io.cosmo.exo

import zio.test.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*
import io.cosmo.exo.categories.*

import scala.util.NotGiven

object IsoTest extends ZIOSpecDefault {

  opaque type Int1 = Int
  object Int1:
    given (Int1 <=> Int) = Iso.refl

  opaque type Int2 = Int
  object Int2:
    given (Int2 <=> Int) = Iso.refl

  def spec = suite("Disjunction")(
    test("toEither") {

      summon[HasIso[Function, Int1, Int]]
      summon[HasIso[Function, Int, Int1]]
      summon[HasIso[* => *, Int, Int]]

      summon[NotGiven[HasIso[Function, Int, String]]]

      summon[Int === Int]

      summon[Int =!= Long]
      summon[NotGiven[Int =!= Int]]
//      summon[Int =!= Int]


      assertTrue(1 == 1)
    }
  )
}
