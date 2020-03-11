package io.cosmo.exo.categories.instances

import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors._
import ProdcatHelpers._

trait ProdcatInstances extends ProdcatInstances01 {
  implicit def prodcatSubcat[==>[_,_], -->[_,_], TC[_]](implicit
    sub1: Subcat.Aux[==>, TC],
    sub2: Subcat.Aux[-->, TC]
  ): Subcat.Aux[Tuple2Bi[==>, -->, *, *], TC] = new ProdcatSubcat[==>, -->, TC] {val s1 = sub1; val s2 = sub2}

  implicit def prodcatEndoBifunctor[==>[_,_], -->[_,_], Bi[_,_]](implicit
    bi1: Endobifunctor[==>, Bi],
    bi2: Endobifunctor[-->, Bi],
  ): Endobifunctor[Tuple2Bi[==>, -->, *, *], Bi] = new ProdcatEndoBifunctor[==>, -->, Bi] {val eb1 = bi1; val eb2 = bi2}

  implicit def prodcatCartesian[==>[_,_], -->[_,_], P[_,_], TC[_], I](implicit
    b1: Cartesian.Aux[==>, P, TC, I],
    b2: Cartesian.Aux[-->, P, TC, I],
  ): Cartesian.Aux[Tuple2Bi[==>, -->, *, *], P, TC, I] =
    new ProdcatCartesian[==>, -->, P, TC, I] {val a1 = b1; val a2 = b2}
}

trait ProdcatInstances01 extends ProdcatInstances02 {
  implicit def prodcatSemicat[==>[_,_], -->[_,_]](implicit
    semi1: Semicategory[==>],
    semi2: Semicategory[-->]
  ): Semicategory[Tuple2Bi[==>, -->, *, *]] = new ProdcatSemicat[==>, -->] {val s1 = semi1; val s2 = semi2}

  implicit def prodcatMonoidal[==>[_,_], -->[_,_], P[_,_], TC[_], I](implicit
    m1: Monoidal.Aux[==>, P, TC, I],
    m2: Monoidal.Aux[-->, P, TC, I],
  ): Monoidal.Aux[Tuple2Bi[==>, -->, *, *], P, TC, I] = new ProdcatMonoidal[==>, -->, P, TC, I] {val a1 = m1; val a2 = m2}
}

trait ProdcatInstances02 extends ProdcatInstances03 {
  implicit def prodcatSymmetric[==>[_,_], -->[_,_], P[_,_], TC[_]](implicit
    b1: Symmetric.Aux[==>, P, TC],
    b2: Symmetric.Aux[-->, P, TC],
  ): Symmetric.Aux[Tuple2Bi[==>, -->, *, *], P, TC] =
    new ProdcatBraided[==>, -->, P, TC] with Symmetric[Tuple2Bi[==>, -->, *, *], P] {val a1 = b1; val a2 = b2}
}

trait ProdcatInstances03 extends ProdcatInstances04 {
  implicit def prodcatBraided[==>[_,_], -->[_,_], P[_,_], TC[_]](implicit
    b1: Braided.Aux[==>, P, TC],
    b2: Braided.Aux[-->, P, TC],
  ): Braided.Aux[Tuple2Bi[==>, -->, *, *], P, TC] = new ProdcatBraided[==>, -->, P, TC] {val a1 = b1; val a2 = b2}
}

trait ProdcatInstances04 {
  implicit def prodcatAssociative[==>[_,_], -->[_,_], P[_,_], TC[_]](implicit
    as1: Associative.Aux[==>, P, TC],
    as2: Associative.Aux[-->, P, TC],
  ): Associative.Aux[Tuple2Bi[==>, -->, *, *], P, TC] = new ProdcatAssociative[==>, -->, P, TC] {val a1 = as1; val a2 = as2}
}

private[instances] object ProdcatHelpers {

  trait ProdcatSemicat[==>[_,_], -->[_,_]] extends Semicategory[Tuple2Bi[==>, -->, *, *]] {
    protected def s1: Semicategory[==>]
    protected def s2: Semicategory[-->]
    def andThen[A, B, C](ab: (A ==> B, A --> B), bc: (B ==> C, B --> C)) =
      (s1.andThen(ab._1, bc._1), s2.andThen(ab._2, bc._2))
  }

  trait ProdcatSubcat[==>[_,_], -->[_,_], TC0[_]] extends ProdcatSemicat[==>, -->] with Subcat[Tuple2Bi[==>, -->, *, *]] {
    protected def s1: Subcat.Aux[==>, TC0]
    protected def s2: Subcat.Aux[-->, TC0]
    type TC[a] = TC0[a]
    def id[A](implicit A: TC[A])= (s1.id, s2.id)
  }

  trait ProdcatEndoBifunctor[==>[_,_], -->[_,_], Bi[_,_]] extends Endobifunctor[Tuple2Bi[==>, -->, *, *], Bi] {
    protected def eb1: Endobifunctor[==>, Bi]
    protected def eb2: Endobifunctor[-->, Bi]
    val L, R, C = prodcatSemicat(eb1.L, eb2.R)
    def leftMap [A, B, Z](fn: (A ==> Z, A --> Z)) = (eb1.leftMap(fn._1), eb2.leftMap(fn._2))
    def rightMap[A, B, Z](fn: (B ==> Z, B --> Z)) = (eb1.rightMap(fn._1), eb2.rightMap(fn._2))
  }

  trait ProdcatAssociative[==>[_,_], -->[_,_], P[_,_], TC0[_]] extends Associative[Tuple2Bi[==>, -->, *, *], P] {
    protected def a1: Associative.Aux[==>, P, TC0]
    protected def a2: Associative.Aux[-->, P, TC0]
    type TC[a] = TC0[a]
    def C = prodcatSubcat[==>, -->, TC0](a1.C, a2.C)
    def bifunctor = prodcatEndoBifunctor(a1.bifunctor, a2.bifunctor)
    def associate  [X, Y, Z] = (a1.associate, a2.associate)
    def diassociate[X, Y, Z] = (a1.diassociate, a2.diassociate)
  }

  trait ProdcatMonoidal[==>[_,_], -->[_,_], P[_,_], TC0[_], I]
    extends ProdcatAssociative[==>, -->, P, TC0]
    with Monoidal[Tuple2Bi[==>, -->, *, *], P]
  {
    protected def a1: Monoidal.Aux[==>, P, TC0, I]
    protected def a2: Monoidal.Aux[-->, P, TC0, I]
    type Id = I
    def idl[A] = (a1.idl, a2.idl)
    def coidl[A] = (a1.coidl, a2.coidl)
    def idr[A] = (a1.idr, a2.idr)
    def coidr[A] = (a1.coidr, a2.coidr)
  }

  trait ProdcatBraided[==>[_,_], -->[_,_], P[_,_], TC0[_]]
    extends ProdcatAssociative[==>, -->, P, TC0]
    with Braided[Tuple2Bi[==>, -->, *, *], P]
  {
    protected def a1: Braided.Aux[==>, P, TC0]
    protected def a2: Braided.Aux[-->, P, TC0]
    def braid[A, B] = (a1.braid, a2.braid)
  }

  trait ProdcatCartesian[==>[_,_], -->[_,_], P[_,_], TC0[_], I]
    extends ProdcatMonoidal[==>, -->, P, TC0, I]
    with ProdcatBraided[==>, -->, P, TC0]
    with Cartesian[Tuple2Bi[==>, -->, *, *], P]
  {
    protected def a1: Cartesian.Aux[==>, P, TC0, I]
    protected def a2: Cartesian.Aux[-->, P, TC0, I]
    def fst[A, B] = (a1.fst, a2.fst)
    def snd[A, B] = (a1.snd, a2.snd)
    def diag[A] = (a1.diag, a2.diag)
    def &&&[X, Y, Z](f: (X ==> Y, X --> Y), g: (X ==> Z, X --> Z)) = (a1.&&&(f._1, g._1), a2.&&&(f._2, g._2))
  }

}