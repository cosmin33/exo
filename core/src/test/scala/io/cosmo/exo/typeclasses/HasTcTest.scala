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
    val mon2 = the[HasTc[Monad, TypeK[List]]]
    val mon3: Monad[List] = implicitly
    val m5 = the[HasTc.Aux[Monad, TypeK[List], List]]

    val mm2: Monad[List] = the[HasTc[Monad, TypeK[List]]].instance

    def getMonad[F[_]](implicit h: HasTc[Monad, TypeK[F]]): Monad[h.F] = h.instance

    val mr: Monad[Option] = getMonad[Option]

    val res = mr.flatMap(1.some)(a => (a + a).some)
    assert(res == 2.some)

  }


}
