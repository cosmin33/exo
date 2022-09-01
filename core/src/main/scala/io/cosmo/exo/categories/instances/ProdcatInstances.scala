package io.cosmo.exo.categories.instances

import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.categories.Cartesian.Aux
import io.cosmo.exo.evidence.=~~=
import io.cosmo.exo.internal.any._

import ProdcatHelpers._

trait ProdcatInstances extends ProdcatInstances01 {
  implicit def prodcatDistributive[==>[_,_], -->[_,_], P[_,_], PI, S[_,_], SI, TC[_]](implicit
    di1: Distributive.Aux[==>, TC, P, PI, S, SI],
    di2: Distributive.Aux[-->, TC, P, PI, S, SI],
  ): Distributive.Aux[Prodcat[==>, -->, *, *], TC, P, PI, S, SI] =
    new ProdcatDistributive[==>, -->, P, PI, S, SI, TC] {val s1 = di1; val s2 = di2}

  implicit def prodcatEndobifunctor[==>[_,_], -->[_,_], Bi[_,_]](implicit
    bi1: Endobifunctor[==>, Bi],
    bi2: Endobifunctor[-->, Bi],
  ): Endobifunctor[Prodcat[==>, -->, *, *], Bi] = new ProdcatEndoBifunctor[==>, -->, Bi] {val eb1 = bi1; val eb2 = bi2}

  implicit def prodcatCartesian[==>[_,_], -->[_,_], P[_,_], TC[_], I](implicit
    b1: Cartesian.Aux[==>, P, TC, I],
    b2: Cartesian.Aux[-->, P, TC, I],
  ): Cartesian.Aux[Prodcat[==>, -->, *, *], P, TC, I] =
    new ProdcatCartesian[==>, -->, P, TC, I] {val a1 = b1; val a2 = b2}
}

trait ProdcatInstances01 extends ProdcatInstances02 {
  implicit def productGroupoid[==>[_,_], -->[_,_], TC[_]](implicit
    g1: Groupoid.Aux[==>, TC],
    g2: Groupoid.Aux[-->, TC],
  ): Groupoid.Aux[Prodcat[==>, -->, *, *], TC] = new ProdcatGroupoid[==>, -->, TC] {val s1 = g1; val s2 = g2}

  implicit def prodcatMonoidal[==>[_,_], -->[_,_], P[_,_], TC[_], I](implicit
    m1: Monoidal.Aux[==>, P, TC, I],
    m2: Monoidal.Aux[-->, P, TC, I],
  ): Monoidal.Aux[Prodcat[==>, -->, *, *], P, TC, I] = new ProdcatMonoidal[==>, -->, P, TC, I] {val a1 = m1; val a2 = m2}
}

trait ProdcatInstances02 extends ProdcatInstances03 {
  implicit def prodcatCcc[==>[_,_], -->[_,_], TC[_], P[_,_], PI, E[_,_]](implicit
    cc1: Ccc.Aux[==>, TC, P, PI, E],
    cc2: Ccc.Aux[-->, TC, P, PI, E],
  ): Ccc.Aux[Prodcat[==>, -->, *, *], TC, P, PI, E] = new ProdcatCcc[==>, -->, TC, P, PI, E] {val s1 = cc1; val s2 = cc2}

  implicit def prodcatSymmetric[==>[_,_], -->[_,_], P[_,_], TC[_]](implicit
    b1: Symmetric.Aux[==>, P, TC],
    b2: Symmetric.Aux[-->, P, TC],
  ): Symmetric.Aux[Prodcat[==>, -->, *, *], P, TC] =
    new ProdcatBraided[==>, -->, P, TC] with Symmetric[Prodcat[==>, -->, *, *], P] {val a1 = b1; val a2 = b2}
}

trait ProdcatInstances03 extends ProdcatInstances04 {
  implicit def prodcatHasInitialObject[==>[_,_], -->[_,_], C[_], I](implicit
    t1: Initial.Aux[==>, C, I],
    t2: Initial.Aux[-->, C, I],
  ): Initial.Aux[Prodcat[==>, -->, *, *], C, I] = new ProdcatInit[==>, -->, C, I] {val s1 = t1; val s2 = t2}

  implicit def prodcatBraided[==>[_,_], -->[_,_], P[_,_], TC[_]](implicit
    b1: Braided.Aux[==>, P, TC],
    b2: Braided.Aux[-->, P, TC],
  ): Braided.Aux[Prodcat[==>, -->, *, *], P, TC] = new ProdcatBraided[==>, -->, P, TC] {val a1 = b1; val a2 = b2}
}

trait ProdcatInstances04 extends ProdcatInstances05 {
  implicit def prodcatHasTerminalObject[==>[_,_], -->[_,_], C[_], T](implicit
    t1: Terminal.Aux[==>, C, T],
    t2: Terminal.Aux[-->, C, T],
  ): Terminal.Aux[Prodcat[==>, -->, *, *], C, T] = new ProdcatTerm[==>, -->, C, T] {val s1 = t1; val s2 = t2}

  implicit def prodcatAssociative[==>[_,_], -->[_,_], P[_,_], TC[_]](implicit
    as1: Associative.Aux[==>, P, TC],
    as2: Associative.Aux[-->, P, TC],
  ): Associative.Aux[Prodcat[==>, -->, *, *], P, TC] = new ProdcatAssociative[==>, -->, P, TC] {val a1 = as1; val a2 = as2}
}

trait ProdcatInstances05 extends ProdcatInstances06 {
  implicit def prodcatSubcat[==>[_,_], -->[_,_], TC[_]](implicit
    sub1: Subcat.Aux[==>, TC],
    sub2: Subcat.Aux[-->, TC]
  ): Subcat.Aux[Prodcat[==>, -->, *, *], TC] = new ProdcatSubcat[==>, -->, TC] {val s1 = sub1; val s2 = sub2}
}

trait ProdcatInstances06 extends ProdcatInstances07 {
  implicit def prodcatSemicat[==>[_,_], -->[_,_]](implicit
    semi1: Semicategory[==>],
    semi2: Semicategory[-->]
  ): Semicategory[Prodcat[==>, -->, *, *]] = new ProdcatSemicat[==>, -->] {val s1 = semi1; val s2 = semi2}
}

trait ProdcatInstances07 {

}

private[instances] object ProdcatHelpers {

  trait ProdcatSemicat[==>[_,_], -->[_,_]] extends Semicategory[Prodcat[==>, -->, *, *]] {
    protected def s1: Semicategory[==>]
    protected def s2: Semicategory[-->]
    def andThen[A, B, C](ab: (A ==> B, A --> B), bc: (B ==> C, B --> C)) =
      (s1.andThen(ab._1, bc._1), s2.andThen(ab._2, bc._2))
  }

  trait ProdcatSubcat[==>[_,_], -->[_,_], TC0[_]] extends ProdcatSemicat[==>, -->] with Subcat[Prodcat[==>, -->, *, *]] {
    protected def s1: Subcat.Aux[==>, TC0]
    protected def s2: Subcat.Aux[-->, TC0]
    type TC[a] = TC0[a]
    def id[A](implicit A: TC[A])= (s1.id, s2.id)
  }

  trait ProdcatEndoBifunctor[==>[_,_], -->[_,_], Bi[_,_]] extends Endobifunctor[Prodcat[==>, -->, *, *], Bi] {
    protected def eb1: Endobifunctor[==>, Bi]
    protected def eb2: Endobifunctor[-->, Bi]
    override def bimap[A, X, B, Y](left: (A ==> X, A --> X), right: (B ==> Y, B --> Y)): (Bi[A, B] ==> Bi[X, Y], Bi[A, B] --> Bi[X, Y]) =
      (eb1.bimap(left._1, right._1), eb2.bimap(left._2, right._2))
  }

  trait ProdcatAssociative[==>[_,_], -->[_,_], P[_,_], TC0[_]] extends Associative[Prodcat[==>, -->, *, *], P] {
    protected def a1: Associative.Aux[==>, P, TC0]
    protected def a2: Associative.Aux[-->, P, TC0]
    type TC[a] = TC0[a]
    def C = prodcatSubcat[==>, -->, TC0](a1.C, a2.C)
    def bifunctor = prodcatEndobifunctor(a1.bifunctor, a2.bifunctor)
    def associate  [X: TC, Y: TC, Z: TC] = (a1.associate, a2.associate)
    def diassociate[X: TC, Y: TC, Z: TC] = (a1.diassociate, a2.diassociate)
  }

  trait ProdcatMonoidal[==>[_,_], -->[_,_], P[_,_], TC0[_], I]
    extends ProdcatAssociative[==>, -->, P, TC0]
    with Monoidal[Prodcat[==>, -->, *, *], P]
  {
    protected def a1: Monoidal.Aux[==>, P, TC0, I]
    protected def a2: Monoidal.Aux[-->, P, TC0, I]
    type Id = I
    def idl  [A: TC] = (a1.idl, a2.idl)
    def coidl[A: TC] = (a1.coidl, a2.coidl)
    def idr  [A: TC] = (a1.idr, a2.idr)
    def coidr[A: TC] = (a1.coidr, a2.coidr)
  }

  trait ProdcatBraided[==>[_,_], -->[_,_], P[_,_], TC0[_]]
    extends ProdcatAssociative[==>, -->, P, TC0]
    with Braided[Prodcat[==>, -->, *, *], P]
  {
    protected def a1: Braided.Aux[==>, P, TC0]
    protected def a2: Braided.Aux[-->, P, TC0]
    def braid[A: TC, B: TC] = (a1.braid, a2.braid)
  }

  trait ProdcatCartesian[==>[_,_], -->[_,_], P[_,_], TC0[_], I]
    extends ProdcatMonoidal[==>, -->, P, TC0, I]
    with ProdcatBraided[==>, -->, P, TC0]
    with Cartesian[Prodcat[==>, -->, *, *], P]
  {
    protected def a1: Cartesian.Aux[==>, P, TC0, I]
    protected def a2: Cartesian.Aux[-->, P, TC0, I]
    def fst[A: TC, B: TC] = (a1.fst, a2.fst)
    def snd[A: TC, B: TC] = (a1.snd, a2.snd)
    def diag[A: TC] = (a1.diag, a2.diag)
    def &&&[X, Y, Z](f: (X ==> Y, X --> Y), g: (X ==> Z, X --> Z)) = (a1.&&&(f._1, g._1), a2.&&&(f._2, g._2))
  }

  trait ProdcatDistributive[==>[_,_], -->[_,_], P[_,_], PI, S[_,_], SI, TC0[_]]
    extends ProdcatSubcat[==>, -->, TC0]
    with Distributive[Prodcat[==>, -->, *, *], P, S]
  {
    protected def s1: Distributive.Aux[==>, TC0, P, PI, S, SI]
    protected def s2: Distributive.Aux[-->, TC0, P, PI, S, SI]
    type ProductId = PI
    type SumId = SI
    def cartesian: Cartesian.Aux[Prodcat[==>, -->, *, *], P, TC0, PI] =
      prodcatCartesian[==>, -->, P, TC0, PI](s1.cartesian, s2.cartesian)
    def cocartesian: Cocartesian.Aux[Prodcat[==>, -->, *, *], S, TC0, SI] =
        prodcatCartesian(s1.cocartesian, s2.cocartesian) |>
          Prodcat.traverseDualEq[==>, -->].subst[Cartesian.Aux[*[_,_], S, TC0, SI]]
    def distribute[A: TC, B: TC, C: TC] = (s1.distribute, s2.distribute)
  }

  trait ProdcatCcc[==>[_,_], -->[_,_], TC0[_], P[_,_], PI, E[_,_]]
    extends ProdcatSubcat[==>, -->, TC0]
    with Ccc[Prodcat[==>, -->, *, *]]
  {
    protected def s1: Ccc.Aux[==>, TC0, P, PI, E]
    protected def s2: Ccc.Aux[-->, TC0, P, PI, E]
    type |->[a, b] = E[a, b]
    type ⊙[a, b] = P[a, b]
    type ProductId = PI
    def cartesian = prodcatCartesian[==>, -->, P, TC0, PI](s1.cartesian, s2.cartesian)
    def uncurry[A, B, C](f: (A ==> (B |-> C), A --> (B |-> C))) = (s1.uncurry[A, B, C](f._1), s2.uncurry[A, B, C](f._2))
    def curry[A, B, C](f: (⊙[A, B] ==> C, ⊙[A, B] --> C)) = (s1.curry(f._1), s2.curry(f._2))
  }

  trait ProdcatGroupoid[==>[_,_], -->[_,_], TC0[_]]
    extends ProdcatSubcat[==>, -->, TC0]
    with Groupoid[Prodcat[==>, -->, *, *]]
  {
    protected def s1: Groupoid.Aux[==>, TC0]
    protected def s2: Groupoid.Aux[-->, TC0]
    def flip[A, B](f: (A ==> B, A --> B)) = (s1.flip(f._1), s2.flip(f._2))
  }

  trait ProdcatInit[==>[_,_], -->[_,_], C[_], I]
    extends ProdcatSubcat[==>, -->, C]
    with Initial[Prodcat[==>, -->, *, *]]
  {
    protected def s1: Initial.Aux[==>, C, I]
    protected def s2: Initial.Aux[-->, C, I]
    type Initial = I
    def initialTC: C[I] = s1.initialTC
    def initiate[A](implicit A: C[A]): (I ==> A, I --> A) = (s1.initiate, s2.initiate)
  }

  trait ProdcatTerm[==>[_,_], -->[_,_], C[_], T]
    extends ProdcatSubcat[==>, -->, C]
    with Terminal[Prodcat[==>, -->, *, *]]
  {
    protected def s1: Terminal.Aux[==>, C, T]
    protected def s2: Terminal.Aux[-->, C, T]
    type Terminal = T
    def terminalTC = s1.terminalTC
    def terminate[A](implicit A: C[A]) = (s1.terminate, s2.terminate)
  }


}