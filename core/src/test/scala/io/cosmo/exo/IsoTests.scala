package io.cosmo.exo

import cats.Semigroup
import cats.implicits._
import io.cosmo.exo.Iso.{HasIso}
import io.cosmo.exo.categories.conversions.CatsInstances._
import io.cosmo.exo.typeclasses.TypeF
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import shapeless.Refute

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

  test("Iso syntax") {
    assert(6.isoTo[String] == "6")
  }

  test("HasIso implicit search") {
    implicitly[HasIso[* => *, String, Int]]
    implicitly[HasIso[* => *, Int, String]]
    implicitly[HasIso[* => *, Int, Int]]
    implicitly[HasIso[FunK, TypeF[List], TypeF[List]]]
    implicitly[Refute[HasIso[* => *, String, Long]]]
  }

  test("case class <-> tupleN iso derivation") {
    case class Afa[A, F[_]](a: A, fa: F[A])
    val tupleIso: Afa[Int, List] <=> (Int, List[Int]) = Iso.forCaseClass[Afa[Int, List]]
    assert(tupleIso.flip.apply((1, List(2, 3))) == Afa(1, List(2, 3)))
  }

  case class Int1(i: Int)
  trait Y
  trait Z

  locally {

    implicit def isoListVect: <~>[List, Vector] = ∀.mk[List <~> Vector].from(Iso.unsafe(_.toVector, _.toList))
    val lv1: List <~> Vector = implicitly[<~>[List, Vector]]
    //val lv2: List <~> Vector = TypeF[List].isoWith[Vector]
    //assert(lv1 == lv2)


    println("done")
  }

}
