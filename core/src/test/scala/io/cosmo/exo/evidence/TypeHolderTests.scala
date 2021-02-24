package io.cosmo.exo.evidence

import io.cosmo.exo.Void
import io.cosmo.exo.typeclasses.TypeK
import io.estatico.newtype.macros.{newsubtype, newtype}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import shapeless.newtype

class TypeHolderTests extends AnyFunSuite  {

  test("Type holder") {

    val l: TypeK[List] = TypeK[List]

    abstract class ListHolder {
      type T
      def list: List[T]
    }

    final class ListHolderFromH(val b: Boolean = true) {
      type A
      def applyT(ft: TypeHolder[A] => List[A]) = new ListHolder {
        type T = A
        def list = ft(TypeHolder[A])
      }
    }

    def load: ListHolderFromH = new ListHolderFromH

    val lh = load.applyT(t => List.empty[t.T])

    //implicitly[lh.T]

  }


}
