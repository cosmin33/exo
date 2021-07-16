package io.cosmo.exo.categories.data

import io.cosmo.exo./\
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class IndexedProductTests extends AnyFunSuite with Matchers {

  implicitly[ProdLength.Aux[Int, 1]]
  implicitly[ProdLength.Aux[Int /\ Long, 2]]
  implicitly[ProdLength.Aux[String /\ Long, 2]]
  implicitly[ProdLength.Aux[String /\ Long /\ String, 3]]
  implicitly[ProdLength.Aux[Int /\ (String /\ Long), 3]]
  implicitly[ProdLength.Aux[Byte /\ String, 2]]
  implicitly[ProdLength.Aux[Byte /\ (Int /\ String), 3]]
  implicitly[ProdLength.Aux[(Byte /\ Int) /\ String, 3]]
  implicitly[ProdLength.Aux[Int /\ (String /\ Long), 3]]
  implicitly[ProdLength.Aux[(Int, (String, Long)), 3]]
  implicitly[ProdLength.Aux[(Byte /\ Int) /\ (String /\ Long), 4]]

  implicitly[ProdIndex[Byte, 0]]
  implicitly[ProdIndex[Byte /\ Int, 0]]
  implicitly[ProdIndex[Byte /\ Int, 1]]
  implicitly[ProdIndex.AuxT[Byte /\ String /\ Int, 0, Byte]]
  implicitly[ProdIndex.AuxT[Byte /\ String /\ Int, 1, String]]
  implicitly[ProdIndex.AuxT[Byte /\ String /\ Int, 2, Int]]
  implicitly[ProdIndex.AuxT[Byte /\ (String /\ Int), 0, Byte]]
  implicitly[ProdIndex.AuxT[Byte /\ (String /\ Int), 1, String]]
  implicitly[ProdIndex.AuxT[Byte /\ (String /\ Int), 2, Int]]

  test("IndexedProduct") {
    val tup = (1, ("Blah", 2L))
    val p = IndexedProduct(tup)
    val p0: Int = p(0)
    val p1: String = p(1)
    val p2: Long = p(2)
    p0 should be (1)
    p1 should be ("Blah")
    p2 should be (2L)
    val reif = ProdReification[tup.type]
    reif.iso.from(reif.iso.to(tup)) should be (tup)
  }

}
