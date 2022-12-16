package io.cosmo.exo.categories.data

import cats.implicits._
import io.cosmo.exo.ConjunctionModule.IsConjunction
import io.cosmo.exo.categories.data.ProdIndex.AuxT
import io.cosmo.exo.evidence.<~<
import io.cosmo.exo.{/\, <=>, ConjunctionModule, Iso}
import shapeless.ops.hlist.{Length, Prepend, Split, ToTraversable}
import shapeless.{::, HList, HNil, Nat, Refute}
import singleton.ops.{Length => _, _}

trait ProdLength[P] {
  type Length <: XInt
}
object ProdLength {
  type Aux[P, L <: XInt] = ProdLength[P] { type Length = L }

  implicit def impSingle[A](implicit
    ev: Refute[IsConjunction[A]],
    ev2: Refute[A <~< Product]
  ): ProdLength.Aux[A, 1] = new ProdLength[A] { type Length = 1 }

  implicit def impPair[A, B, LA <: XInt, LB <: XInt, LAB <: XInt](implicit
    la: ProdLength.Aux[A, LA],
    lb: ProdLength.Aux[B, LB],
    lab: OpAuxInt[LA + LB, LAB]
  ): ProdLength.Aux[A /\ B, LAB] = new ProdLength[A /\ B] { type Length = LAB }

  implicit def impPairTup[A, B, LA <: XInt, LB <: XInt, LAB <: XInt](implicit
    la: ProdLength.Aux[A, LA],
    lb: ProdLength.Aux[B, LB],
    lab: OpAuxInt[LA + LB, LAB]
  ): ProdLength.Aux[(A, B), LAB] = new ProdLength[(A, B)] { type Length = LAB }

  implicit def impProduct2[P <: Product, A, B](implicit x: P <~< Product2[A, B])
    : ProdLength.Aux[P, 2] = new ProdLength[P] { type Length = 2 }
  implicit def impProduct3[P <: Product, A1, A2, A3](implicit x: P <~< Product3[A1, A2, A3])
    : ProdLength.Aux[P, 3] = new ProdLength[P] { type Length = 3 }

}

trait ProdReification[P] {
  type H <: HList
  def iso: P <=> H
}
object ProdReification {
  type Aux[P, H0 <: HList] = ProdReification[P] { type H = H0 }

  def apply[P](implicit r: ProdReification[P]): ProdReification.Aux[P, r.H] = r

  implicit def impSingle[A](implicit ev: Refute[IsConjunction[A]]): ProdReification.Aux[A, A :: HNil] =
    new ProdReification[A] {
      type H = A :: HNil
      def iso = Iso.unsafe(_ :: HNil, _.head)
    }

  implicit def impPair[A, B, HA <: HList, HB <: HList, HAB <: HList, LA <: Nat](implicit
    pa: ProdReification.Aux[A, HA],
    pb: ProdReification.Aux[B, HB],
    prep: Prepend.Aux[HA, HB, HAB],
    la: Length.Aux[HA, LA],
    split: Split.Aux[HAB, LA, HA, HB]
  ): ProdReification.Aux[A /\ B, HAB] =
    new ProdReification[A /\ B] {
      type H = HAB
      def iso: (A /\ B) <=> HAB =
        Iso.unsafe(
          p => prep(pa.iso.to(p._1), pb.iso.to(p._2)),
          hab => /\(undoPrepend[HA, HB](prep, la).apply(hab).bimap(pa.iso.from, pb.iso.from))
        )
    }

  implicit def impPairTup[A, B, HA <: HList, HB <: HList, HAB <: HList, LA <: Nat](implicit
    pa: ProdReification.Aux[A, HA],
    pb: ProdReification.Aux[B, HB],
    hab: Prepend.Aux[HA, HB, HAB],
    la: Length.Aux[HA, LA],
    split: Split.Aux[HAB, LA, HA, HB]
  ): ProdReification.Aux[(A, B), HAB] =
    ConjunctionModule.typeclassToTuple[ProdReification.Aux[*, HAB], A, B](impPair(pa, pb, hab, la, split))

  class UndoPrependHelper[A <: HList, B <: HList, C <: HList, N <: Nat] {
    def apply(c: C)(implicit split: Split.Aux[C, N, A, B]): (A, B) = split(c)
  }

  def undoPrepend[A <: HList, B <: HList](implicit
    prepend: Prepend[A, B],
    length: Length[A]
  ) = new UndoPrependHelper[A, B, prepend.Out, length.Out]

  def iso[P1, P2, H <: HList](implicit
    l1: ProdReification.Aux[P1, H],
    l2: ProdReification.Aux[P2, H],
  ): P1 <=> P2 = l1.iso.andThen(l2.iso.flip)

}

trait ProdIndex[P, I] {
  type Length <: XInt
  val len: ProdLength.Aux[P, Length]
  def ev: Require[(I >= 0) && (I < Length)]
  type T
  def get(prod: P): T
  def set(prod: P, value: T): P
}
object ProdIndex {
  type Aux[P, I, T0, L] = ProdIndex[P, I] { type T = T0; type Length = L }
  type AuxT[P, I, T0] = ProdIndex[P, I] { type T = T0 }

  implicit def impSingle[A](implicit ev: Refute[A <~< Product], l: ProdLength.Aux[A, 1]): ProdIndex.Aux[A, 0, A, 1] =
    new ProdIndex[A, 0] {
      type Length = 1
      val len = l
      val ev = implicitly
      type T = A
      def get(prod: A) = prod
      def set(prod: A, value: T) = value
    }

  implicit def impPairA[A, B, IA <: XInt, TA, LA <: XInt, LB <: XInt, LAB <: XInt](implicit
    i1: ProdIndex.Aux[A, IA, TA, LA],
    l2: ProdLength.Aux[B, LB],
    ll: OpAuxInt[LA + LB, LAB],
    proof: Require[IA >= 0 && (IA < LAB)]
  ): ProdIndex.Aux[A /\ B, IA, TA, LAB] =
    new ProdIndex[A /\ B, IA] {
      type Length = LAB
      val len: ProdLength.Aux[A /\ B, LAB] = ProdLength.impPair(i1.len, l2, ll)
      override def ev: Require[IA >= 0 && (IA < LAB)] = proof
      type T = TA
      def get(prod: A /\ B): TA = i1.get(prod._1)
      def set(prod: A /\ B, value: TA): A /\ B = /\(i1.set(prod._1, value), prod._2)
    }
  implicit def impPairATup[A, B, IA <: XInt, TA, LA <: XInt, LB <: XInt, LAB <: XInt](implicit
    i1: ProdIndex.Aux[A, IA, TA, LA],
    l2: ProdLength.Aux[B, LB],
    ll: OpAuxInt[LA + LB, LAB],
    proof: Require[IA >= 0 && (IA < LAB)]
  ): ProdIndex.Aux[(A, B), IA, TA, LAB] = ConjunctionModule.typeclassToTuple[ProdIndex.Aux[*, IA, TA, LAB], A, B]

  implicit def impPairB[A, B, IB <: XInt, TB, LA <: XInt, LB <: XInt, IB1 <: XInt, LAB <: XInt](implicit
    l1: ProdLength.Aux[A, LA],
    ib: OpAuxInt[IB1 - LA, IB],
    i2: ProdIndex.Aux[B, IB, TB, LB],
    ll: OpAuxInt[LA + LB, LAB],
    proof: Require[IB1 >= 0 && (IB1 < LAB)]
  ): ProdIndex.Aux[A /\ B, IB1, TB, LAB] =
    new ProdIndex[A /\ B, IB1] {
      type Length = LAB
      val len = ProdLength.impPair(l1, i2.len, ll)
      def ev: Require[IB1 >= 0 && (IB1 < LAB)] = proof
      type T = TB
      def get(prod: A /\ B): TB = i2.get(prod._2)
      def set(prod: A /\ B, value: TB): A /\ B = /\(prod._1, i2.set(prod._2, value))
    }
  implicit def impPairBTup[A, B, IB <: XInt, TB, LA <: XInt, LB <: XInt, IB1 <: XInt, LAB <: XInt](implicit
    l1: ProdLength.Aux[A, LA],
    ib: OpAuxInt[IB1 - LA, IB],
    i2: ProdIndex.Aux[B, IB, TB, LB],
    ll: OpAuxInt[LA + LB, LAB],
    proof: Require[IB1 >= 0 && (IB1 < LAB)]
  ): ProdIndex.Aux[(A, B), IB1, TB, LAB] = ConjunctionModule.typeclassToTuple[ProdIndex.Aux[*, IB1, TB, LAB], A, B]
}

trait IndexedProduct[P] {
  type Length <: XInt
  def pl: ProdLength.Aux[P, Length]
  def apply[I <: XInt, T](i: I)(implicit pi: ProdIndex.AuxT[P, I, T]): T
}
object IndexedProduct {
  type Aux[P, L] = IndexedProduct[P] { type Length = L }
  def apply[P, L <: XInt, H <: HList](p: P)(implicit
    l: ProdLength.Aux[P, L],
    reif: ProdReification.Aux[P, H],
    tol: ToTraversable[H, Vector]
  ): IndexedProduct[P] = new IndexedProduct[P] {
    type Length = L
    def pl: ProdLength.Aux[P, L] = l
    val data: Vector[Any] = reif.iso.to(p).to[Vector]
    def apply[I <: XInt, T](i: I)(implicit pi: ProdIndex.AuxT[P, I, T]) = data(i).asInstanceOf[T]
  }

  def from2[P <: Product, A1, A2, L <: XInt](p: P)(implicit l: ProdLength.Aux[P, L], ev: P <~< Product2[A1, A2]): IndexedProduct.Aux[P, L] =
    new IndexedProduct[P] {
      type Length = L
      def pl: ProdLength.Aux[P, L] = l
      def apply[I <: XInt, T](i: I)(implicit pi: ProdIndex.AuxT[P, I, T]) = p.productElement(i).asInstanceOf[T]
    }

  def from3[P <: Product, A1, A2, A3, L <: XInt](p: P)(implicit l: ProdLength.Aux[P, L], ev: P <~< Product3[A1, A2, A3]): IndexedProduct.Aux[P, L] =
    new IndexedProduct[P] {
      type Length = L
      def pl: ProdLength.Aux[P, L] = l
      def apply[I <: XInt, T](i: I)(implicit pi: ProdIndex.AuxT[P, I, T]) = p.productElement(i).asInstanceOf[T]
    }


  case class Person(id: Int, name: String, address: String) extends Product3[Int, String, String] {
    def _1 = id
    def _2 = name
    def _3 = address
  }

  val ip: IndexedProduct.Aux[Person, 3] = from3(Person(1, "Jotun", "Jotunheim"))
//  val personId = ip(0)
//  val personName = ip(1)
//  val personAddres = ip(2)


}
