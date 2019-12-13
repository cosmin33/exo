package io.cosmo.exo

import cats.data.Kleisli
import io.cosmo.exo.evidence._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite

class SigmaTests extends AnyFunSuite with Matchers {

  test("sigma tests") {

    val sigma: Sigma[Nil.type, * <:< List[Int]] = Sigma.summon[λ[x => x <:< List[Int]]](Nil)

    val sig = Sigma.summon[* <:< List[Int]](Nil)
    val xx: Nil.type <:< List[Int] = sig.second

    implicitly[Nil.type <:< List[Int]]
    implicitly[Nil.type <~< List[Long]]

    //val ll: TypeF[List] = TypeF.apply[List]


  }

}