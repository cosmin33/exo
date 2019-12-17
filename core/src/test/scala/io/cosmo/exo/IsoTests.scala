package io.cosmo.exo

import cats.Semigroup
import cats.implicits._
import io.cosmo.exo.Iso.{Aux, AuxTF, HasIso}
import io.cosmo.exo.categories.Trivial.T1
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
import io.cosmo.exo.categories._
import io.cosmo.exo.evidence._
import io.cosmo.exo.typeclasses.TypeF
import shapeless.{Refute, tag}
import shapeless.tag.@@
    import io.cosmo.exo.categories.conversions.CatsInstances._

class IsoTests extends AnyFunSuite with Matchers {

  implicit val isoIL: Int <=> Long = Iso.unsafe(_.toLong, _.toInt)
  implicit val isoSI: String <=> Int = Iso.unsafe(_.toInt, _.toString)

  test("derive") {
    val sl: Semigroup[Long] = isoIL.derive[Semigroup]
    assert(sl.combine(1L, 2L) == 3L)
  }

  test("chain") {
    assert(isoSI.chain[Long].flip.chain[String].chain[String].apply(4L) == "4")
  }

  test("HasIso implicit search") {
    implicitly[HasIso[* => *, String, Int]]
    implicitly[HasIso[* => *, Int, String]]
    implicitly[HasIso[* => *, Int, Int]]
  }

  test("case class <-> tupleN iso derivation") {
    case class Afa[A, F[_]](a: A, fa: F[A])
    val tupleIso: Afa[Int, List] <=> (Int, List[Int]) = Iso.forCaseClass[Afa[Int, List]]
    assert(tupleIso.from((1, List(2, 3))) == Afa(1, List(2, 3)))
  }

  case class Int1(i: Int)
  trait Y
  trait Z

  locally {

    implicit def isoListVect: <~>[List, Vector] = ∀.mk[List <~> Vector].from(Iso.unsafeT(_.toVector, _.toList))
    implicitly[<~>[List, Vector]]


    println("done")
  }

}
