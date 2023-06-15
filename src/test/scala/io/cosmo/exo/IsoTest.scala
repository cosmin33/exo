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

  opaque type List1[A] = List[A]
  object List1:
    given [A]: (List1[A] <=> List[A]) = Iso.refl

  opaque type Map1[A, B] = Map[A, B]
  object Map1:
    given [A, B]: (Map1[A, B] <=> Map[A, B]) = Iso.refl

  def spec = suite("Disjunction")(
    test("toEither") {

      summon[HasIso[Function, Int1, Int]]
      summon[HasIso[Function, Int, Int1]]
      summon[HasIso[* => *, Int, Int]]

      summon[NotGiven[HasIso[Function, Int, String]]]

      summon[HasIsoK[Function, List1, List]]
      summon[HasIsoK[Function, List, List]]
      def xx[F[_]]: ∀[[a] =>> Trivial[F[a]]] = summon[∀[[a] =>> Trivial[F[a]]]]
      summon[ReflImpIsoK[Function, List]]
      summon[NotGiven[HasIsoK[Function, List1, Option]]]

      summon[HasIsoK2[Function, Map1, Map]]
      summon[HasIsoK2[Function, Map, Map]]
      summon[NotGiven[HasIsoK2[Function, Map1, Either]]]

      summon[Int === Int]

      summon[Int =!= Long]
      summon[NotGiven[Int =!= Int]]


      assertTrue(1 == 1)
    }
  )
}
