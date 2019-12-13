package io.cosmo.exo.evidence.variance

import io.cosmo.exo._
import io.cosmo.exo.evidence.{</<, StrictAs}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import shapeless.Refute

class VarianceTests extends AnyFunSuite with Matchers {

  test("covariance") {

    val rr: Void </< Any = StrictAs.bottomTop

    IsCovariant[Option]
    IsCovariant[List]
    IsCovariant[λ[`+x` => x]]
    implicitly[IsCovariant[Option]]
    implicitly[IsCovariant[List]]
    implicitly[IsCovariant[λ[`+x` => x]]]
  }

  test("strict covariance") {
    StrictlyCovariant[Option]
    StrictlyCovariant[List]
    StrictlyCovariant[λ[`+x` => x]]
    implicitly[StrictlyCovariant[Option]]
    implicitly[StrictlyCovariant[List]]
    implicitly[StrictlyCovariant[λ[`+x` => x]]]

    implicitly[Refute[StrictlyContravariant[λ[`+x` => x]]]]
    implicitly[Refute[StrictlyContravariant[λ[x => x]]]]
  }

  test("contravariance") {
    type f[-x] = x => Boolean
    IsContravariant[f]
  }

  test("strict contravariance") {
    type f[-x] = x => Boolean
    StrictlyContravariant[f]
  }



}
