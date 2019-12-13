package io.cosmo.exo.evidence

import cats.Monad
import cats.implicits._
import io.cosmo.exo._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
import shapeless.Refute

class InhabitanceTests  extends AnyFunSuite with Matchers {

  test("propositions") {
    implicitly[Proposition[Unit]]
    implicitly[Proposition["singleton"]]
    implicitly[Proposition[76]]
    implicitly[Inhabited[Unit]]
    implicitly[Inhabited["singleton"]]
    implicitly[Inhabited[76]]
  }

  test("inhabitance") {

    implicitly[Inhabited[Any]]

    Inhabited[Any]
    Inhabited[AnyVal]
    Inhabited[AnyRef]
    Inhabited[0]
    val x0: Int = 0
    Inhabited[x0.type]
    Inhabited[this.type] : Inhabited[this.type]
    Inhabited["abc"]
    Inhabited[Int]
    Inhabited[String]
    implicitly[Inhabited[Any]]
    implicitly[Inhabited[AnyVal]]
    implicitly[Inhabited[AnyRef]]
    implicitly[Inhabited[0]]
    implicitly[Inhabited[x0.type]]
    implicitly[Inhabited[this.type]]
    implicitly[Inhabited["abc"]]
    implicitly[Inhabited[Int]]
    implicitly[Inhabited[String]]

    implicitly[Refute[Inhabited[Void]]]


    implicit val imo: Inhabited[Monad[Option]] = Inhabited.value(Monad[Option])
    implicitly[Inhabited[Monad[Option]]]

  }

  test("uninhabitance") {
    Uninhabited[Void]
    Uninhabited[Int => Void]
    Uninhabited[Int => String => Void]
    implicitly[Uninhabited[Void]]
    implicitly[Uninhabited[Int => Void]]
    implicitly[Uninhabited[Int => String => Void]]

    implicitly[Refute[Uninhabited[Unit]]]
  }

}
