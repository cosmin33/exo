package io.cosmo.exo.categories.data

import io.cosmo.exo./\
import io.cosmo.exo.ConjunctionModule.IsConjunction
import io.cosmo.exo.categories.Associative
import io.cosmo.exo.categories.functors.LaxSemigroupal
import io.cosmo.exo.evidence.===
import shapeless.{HList, Refute}
import shapeless.ops.hlist.{Length => Len}
import singleton.ops._

import scala.collection.immutable.ArraySeq

trait ProdLength[P] {
  type Length <: XInt
}
object ProdLength {
  type Aux[P, L <: XInt] = ProdLength[P] { type Length = L }

  implicit def impSingle[A](implicit ev: Refute[IsConjunction[A]]): ProdLength.Aux[A, 1] = new ProdLength[A] { type Length = 1 }

  implicit def impPair[A, B, LA <: XInt, LB <: XInt](implicit
    la: ProdLength.Aux[A, LA],
    lb: ProdLength.Aux[B, LB],
    lab: LA + LB
  ): ProdLength.Aux[A /\ B, lab.OutInt] = new ProdLength[A /\ B] {
    type Length = lab.OutInt
  }

  implicitly[ProdLength.Aux[Int, 1]]
  implicitly[ProdLength.Aux[Int /\ Long, 2]]
  implicitly[ProdLength.Aux[String /\ Long, 2]]
  implicitly[ProdLength.Aux[String /\ Long /\ String, 3]]
  implicitly[ProdLength.Aux[Int /\ (String /\ Long), 3]]
  implicitly[ProdLength.Aux[Byte /\ String, 2]]
  implicitly[ProdLength.Aux[Byte /\ (Int /\ String), 3]]
  implicitly[ProdLength.Aux[(Byte /\ Int) /\ String, 3]]
  implicitly[ProdLength.Aux[Int /\ (String /\ Long), 3]]
  implicitly[ProdLength.Aux[(Byte /\ Int) /\ (String /\ Long), 4]]

}


trait ProdIndex[P, I] {
  type Length <: XInt
  val len: ProdLength.Aux[P, Length]
  def ev: Require[(I >= 0) && (I < Length)]
  type T
}
object ProdIndex {
  type Aux[P, I, T0] = ProdIndex[P, I] { type T = T0 }
  type Aux1[P, I, T0, L] = ProdIndex[P, I] { type T = T0; type Length = L }

  implicit def impSingle[A](implicit l: ProdLength.Aux[A, 1]): ProdIndex.Aux1[A, 0, A, 1] =
    new ProdIndex[A, 0] {
      type Length = 1
      val len = l
      val ev = implicitly
      type T = A
    }

  implicit def impPairA[A, B, IA <: XInt, TA, LA <: XInt, LB <: XInt](implicit
    i1: ProdIndex.Aux1[A, IA, TA, LA],
    l2: ProdLength.Aux[B, LB],
    l: LA + LB
  ): ProdIndex.Aux1[A /\ B, IA, TA, l.OutInt] =
    new ProdIndex[A /\ B, IA] {
      type Length = l.OutInt
      val len = ProdLength.impPair(i1.len, l2, l)
      def ev: Require[IA >= 0 && (IA < l.OutInt)] = implicitly[Require[0 >= 0]].asInstanceOf // TODO: verify !!!
      type T = TA
    }

  implicit def impPairB[A, B, IB <: XInt, TB, LA <: XInt, LB <: XInt](implicit
    l1: ProdLength.Aux[A, LA],
    i2: ProdIndex.Aux1[B, IB, TB, LB],
    l: LA + LB,
    ib1: LA + IB
  ): ProdIndex.Aux1[A /\ B, ib1.OutInt, TB, l.OutInt] =
    new ProdIndex[A /\ B, ib1.OutInt] {
      type Length = l.OutInt
      val len = ProdLength.impPair(l1, i2.len, l)
      def ev: Require[ib1.OutInt >= 0 && (ib1.OutInt < l.OutInt)] = implicitly[Require[0 >= 0]].asInstanceOf // TODO: verify !!!
      type T = TB
    }

  implicitly[ProdIndex[Byte, 0]]
  implicitly[ProdIndex[Byte /\ Int, 0]]
  implicitly[ProdIndex[Byte /\ Int, 1]]
  //implicitly[ProdIndex[Byte /\ (String /\ Int), 0]]

}

trait TupleN[P] {
  type Length <: XInt
  val pl: ProdLength.Aux[P, Length]
  def data: ArraySeq[Any]
  def apply[I <: XInt, T](i: I)(implicit pi: ProdIndex.Aux[P, I, T]): T = data(i).asInstanceOf[T]
}
object TupleN {

}
