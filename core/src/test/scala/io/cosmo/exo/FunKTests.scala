package io.cosmo.exo

import cats.Eq
import cats.arrow.Category.ToCategoryOps
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import io.cosmo.exo._
import io.cosmo.exo.categories.{Cartesian, Cocartesian}
import io.cosmo.exo.categories.syntax._
import io.cosmo.exo.evidence._
import io.cosmo.exo.typeclasses.TypeF


class FunKTests extends AnyFunSuite with Matchers {
  test("Funktion tests") {
    val f1: List ~> Option = ∀.mk[List ~> Option].from(_.headOption)
    val f2: Vector ~> Option = ∀.mk[Vector ~> Option].from(_.headOption)
    val f3: List ~> Vector = ∀.mk[List ~> Vector].from(_.toVector)
    val f4: List ~> List = ∀.mk[List ~> List].from(identity)

    val y1: λ[α => Either[List[α], Vector[α]]] ~> Option = FunK(f1).split(FunK(f2)).unapply
    val y2: List ~> λ[α => (Option[α], Vector[α])] = FunK(f1).merge(FunK(f3)).unapply

    val y3: FunK[TypeF[List], ((TypeF[Option], TypeF[Vector]), TypeF[List])] = FunK(f1).merge(FunK(f3)).merge(FunK(f4))
    val y4: List ~> λ[α => ((Option[α], Vector[α]), List[α])] = y3.unapply

    val m0: List ~> λ[α => ((Option[α], Vector[α]), List[α])] = (FunK(f1) merge FunK(f3) merge FunK(f4)).unapply

    val yy: List ~> λ[α => (Option[α], (Vector[α], List[α]))] = FunK(f1).merge3(FunK(f3), FunK(f4)).unapply

    val l = List(1)
    val rl: (Option[Int], (Vector[Int], List[Int])) = yy.apply[Int].apply(l)

  }
}
