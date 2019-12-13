package io.cosmo.exo.typeclasses

import cats.Monad
import cats.evidence.===
import cats.implicits._
import io.cosmo.exo.{ExistsK1, ExistsK2}
import org.scalatest.funsuite.AnyFunSuite
import shapeless.the

class HasTcTest extends AnyFunSuite {

  test("HasTc") {
    val mon1: Monad[List] = the[Monad[List]]
    val mon2 = the[HasTc[Monad, TypeF[List]]]
    val mon3: Monad[List] = implicitly
    val m5 = the[HasTc.Aux[Monad, TypeF[List], List]]

    val mm2: Monad[List] = the[HasTc[Monad, TypeF[List]]].instance

    def getMonad[F[_]](implicit h: HasTc[Monad, TypeF[F]]): Monad[h.F] = h.instance

    val mr: Monad[Option] = getMonad[Option]

    val res = mr.flatMap(1.some)(a => (a + a).some)
    assert(res == 2.some)

    the[HasTypeclass[TypeH[Monad], TypeF[Option]]]

  }

  test("temporary") {

    val l: TypeF[List] = TypeF[List]

    implicitly[Monad[List]]
  }

}
