package io.cosmo.exo.internal

import io.cosmo.exo.categories.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.any.*
import io.cosmo.exo.evidence.*

import ProdcatInstances.*

trait ProdcatSemicategoryInstances extends ProdcatSemicategoryInstances01 {
  given prodcatDistributive[==>[_,_], -->[_,_], P[_,_], PI, S[_,_], SI, TC[_]](using
    Distributive.Aux[==>, TC, P, PI, S, SI],
    Distributive.Aux[-->, TC, P, PI, S, SI],
  ): Distributive.Aux[Prodcat[==>, -->, *, *], TC, P, PI, S, SI] = ProdcatDistributive[==>, -->, P, PI, S, SI, TC]

}
trait ProdcatSemicategoryInstances01 extends ProdcatSemicategoryInstances02 {
  given productGroupoid[==>[_,_], -->[_,_], TC[_]](using
    Groupoid.Aux[==>, TC],
    Groupoid.Aux[-->, TC],
  ): Groupoid.Aux[Prodcat[==>, -->, *, *], TC] = ProdcatGroupoid[==>, -->, TC]
}
trait ProdcatSemicategoryInstances02 extends ProdcatSemicategoryInstances03 {
  given prodcatSubcat[==>[_,_], -->[_,_], TC[_]](using
    Subcat.Aux[==>, TC],
    Subcat.Aux[-->, TC]
  ): Subcat.Aux[Prodcat[==>, -->, *, *], TC] = ProdcatSubcat[==>, -->, TC]
}
trait ProdcatSemicategoryInstances03 extends ProdcatSemicategoryInstances04 {
  given prodcatSemicat[==>[_,_]: Semicategory, -->[_,_]: Semicategory]: Semicategory[Prodcat[==>, -->, *, *]] =
    ProdcatSemicat[==>, -->]
}
trait ProdcatSemicategoryInstances04 extends ProdcatSemicategoryInstances05 {
}
trait ProdcatSemicategoryInstances05 {
}

trait ProdcatBifunctorInstances {
  given prodcatEndobifunctor[==>[_,_], -->[_,_], Bi[_,_]](using
    Endobifunctor[==>, Bi],
    Endobifunctor[-->, Bi],
  ): Endobifunctor[Prodcat[==>, -->, *, *], Bi] = ProdcatEndoBifunctor[==>, -->, Bi]
}

trait ProdcatAssociativeInstances extends ProdcatAssociativeInstances01 {
  given prodcatCcc[==>[_,_], -->[_,_], TC[_], P[_,_], PI, E[_,_]](using
    cc1: Ccc.Aux[==>, P, TC, PI, E],
    cc2: Ccc.Aux[-->, P, TC, PI, E],
  ): Ccc.Aux[Prodcat[==>, -->, *, *], P, TC, PI, E] = ProdcatCcc[==>, -->, TC, P, PI, E]
}
trait ProdcatAssociativeInstances01 extends ProdcatAssociativeInstances02 {
  given prodcatCartesian[==>[_,_], -->[_,_], P[_,_], TC[_], I](using
    b1: Cartesian.Aux[==>, P, TC, I],
    b2: Cartesian.Aux[-->, P, TC, I],
  ): Cartesian.Aux[Prodcat[==>, -->, *, *], P, TC, I] = ProdcatCartesian[==>, -->, P, TC, I]
}
trait ProdcatAssociativeInstances02 extends ProdcatAssociativeInstances03 {
  given prodcatMonoidal[==>[_,_], -->[_,_], P[_,_], TC[_], I](using
    b1: Monoidal.Aux[==>, P, TC, I],
    b2: Monoidal.Aux[-->, P, TC, I],
  ): Monoidal.Aux[Prodcat[==>, -->, *, *], P, TC, I] = ProdcatMonoidal[==>, -->, P, TC, I]
}
trait ProdcatAssociativeInstances03 extends ProdcatAssociativeInstances04 {
  given prodcatSymmetric[==>[_,_], -->[_,_], P[_,_], TC[_]](using
    b1: Symmetric.Aux[==>, P, TC],
    b2: Symmetric.Aux[-->, P, TC],
  ): Symmetric.Aux[Prodcat[==>, -->, *, *], P, TC] =
    new ProdcatBraided[==>, -->, P, TC] with Symmetric[Prodcat[==>, -->, *, *], P] {val a1 = b1; val a2 = b2}
}
trait ProdcatAssociativeInstances04 extends ProdcatAssociativeInstances05 {
  given prodcatBraided[==>[_,_], -->[_,_], P[_,_], TC[_]](using
    Braided.Aux[==>, P, TC],
    Braided.Aux[-->, P, TC],
  ): Braided.Aux[Prodcat[==>, -->, *, *], P, TC] = ProdcatBraided[==>, -->, P, TC]
}
trait ProdcatAssociativeInstances05 extends ProdcatAssociativeInstances06 {
  given prodcatAssociative[==>[_,_], -->[_,_], P[_,_], TC[_]](using
    as1: Associative.Aux[==>, P, TC],
    as2: Associative.Aux[-->, P, TC],
  ): Associative.Aux[Prodcat[==>, -->, *, *], P, TC] = ProdcatAssociative[==>, -->, P, TC]
}
trait ProdcatAssociativeInstances06 {

}

trait ProdcatInitialTerminalInstances {
  given prodcatHasInitialObject[==>[_,_], -->[_,_], C[_], I](using
    t1: Initial.Aux[==>, C, I],
    t2: Initial.Aux[-->, C, I],
  ): Initial.Aux[Prodcat[==>, -->, *, *], C, I] = ProdcatInit[==>, -->, C, I]

  given prodcatHasTerminalObject[==>[_,_], -->[_,_], C[_], T](using
    t1: Terminal.Aux[==>, C, T],
    t2: Terminal.Aux[-->, C, T],
  ): Terminal.Aux[Prodcat[==>, -->, *, *], C, T] = ProdcatTerm[==>, -->, C, T]
}

object ProdcatInstances {

  trait ProdcatSemicat[==>[_,_], -->[_,_]] extends Semicategory[Prodcat[==>, -->, *, *]] {
    protected def s1: Semicategory[==>]
    protected def s2: Semicategory[-->]
    def andThen[A, B, C](ab: (A ==> B, A --> B), bc: (B ==> C, B --> C)) =
      (s1.andThen(ab._1, bc._1), s2.andThen(ab._2, bc._2))
  }
  object ProdcatSemicat:
    def apply[==>[_,_], -->[_,_]](using
      s1: Semicategory[==>],
      s2: Semicategory[-->],
    ): Semicategory[Prodcat[==>, -->, *, *]] =
      new ProdcatSemicat[==>, -->] {val s1 = s1; val s2 = s2}

  trait ProdcatSubcat[==>[_,_], -->[_,_], TC0[_]] extends ProdcatSemicat[==>, -->] with Subcat[Prodcat[==>, -->, *, *]] {
    protected def s1: Subcat.Aux[==>, TC0]
    protected def s2: Subcat.Aux[-->, TC0]
    type TC[a] = TC0[a]
    def id[A](using A: TC[A])= (s1.id, s2.id)
  }
  object ProdcatSubcat:
    def apply[==>[_,_], -->[_,_], TC0[_]](using
      s1: Subcat.Aux[==>, TC0],
      s2: Subcat.Aux[-->, TC0],
    ): Subcat.Aux[Prodcat[==>, -->, *, *], TC0] =
      new ProdcatSubcat[==>, -->, TC0] {val s1 = s1; val s2 = s2}

  trait ProdcatEndoBifunctor[==>[_,_], -->[_,_], Bi[_,_]] extends Endobifunctor[Prodcat[==>, -->, *, *], Bi] {
    protected def eb1: Endobifunctor[==>, Bi]
    protected def eb2: Endobifunctor[-->, Bi]
    override def bimap[A, X, B, Y](left: (A ==> X, A --> X), right: (B ==> Y, B --> Y)): (Bi[A, B] ==> Bi[X, Y], Bi[A, B] --> Bi[X, Y]) =
      (eb1.bimap(left._1, right._1), eb2.bimap(left._2, right._2))
  }
  object ProdcatEndoBifunctor:
    def apply[==>[_,_], -->[_,_], Bi[_,_]](using
      eb1: Endobifunctor[==>, Bi],
      eb2: Endobifunctor[-->, Bi],
    ): Endobifunctor[Prodcat[==>, -->, *, *], Bi] =
      new ProdcatEndoBifunctor[==>, -->, Bi] {val eb1 = eb1; val eb2 = eb2}

  trait ProdcatAssociative[==>[_,_], -->[_,_], P[_,_], TC0[_]] extends Associative[Prodcat[==>, -->, *, *], P] {
    protected def a1: Associative.Aux[==>, P, TC0]
    protected def a2: Associative.Aux[-->, P, TC0]
    type TC[a] = TC0[a]
    def C = ProdcatSubcat[==>, -->, TC0](using a1.C, a2.C)
    def bifunctor = ProdcatEndoBifunctor(using a1.bifunctor, a2.bifunctor)
    def associate  [X: TC, Y: TC, Z: TC] = (a1.associate, a2.associate)
    def diassociate[X: TC, Y: TC, Z: TC] = (a1.diassociate, a2.diassociate)
  }
  object ProdcatAssociative:
    def apply[==>[_,_], -->[_,_], P[_,_], TC0[_]](using
      a1: Associative.Aux[==>, P, TC0],
      a2: Associative.Aux[-->, P, TC0],
    ): Associative.Aux[Prodcat[==>, -->, *, *], P, TC0] =
      new ProdcatAssociative[==>, -->, P, TC0] {val a1 = a1; val a2 = a2}

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
  object ProdcatMonoidal:
    def apply[==>[_,_], -->[_,_], P[_,_], TC0[_], I](using
      a1: Monoidal.Aux[==>, P, TC0, I],
      a2: Monoidal.Aux[-->, P, TC0, I],
    ): Monoidal.Aux[Prodcat[==>, -->, *, *], P, TC0, I] =
      new ProdcatMonoidal[==>, -->, P, TC0, I] {val a1 = a1; val a2 = a2}

  trait ProdcatBraided[==>[_,_], -->[_,_], P[_,_], TC0[_]]
    extends ProdcatAssociative[==>, -->, P, TC0]
    with Braided[Prodcat[==>, -->, *, *], P]
  {
    protected def a1: Braided.Aux[==>, P, TC0]
    protected def a2: Braided.Aux[-->, P, TC0]
    def braid[A: TC, B: TC] = (a1.braid, a2.braid)
  }
  object ProdcatBraided:
    def apply[==>[_,_], -->[_,_], P[_,_], TC0[_]](using
      a1: Braided.Aux[==>, P, TC0],
      a2: Braided.Aux[-->, P, TC0],
    ): Braided.Aux[Prodcat[==>, -->, *, *], P, TC0] =
      new ProdcatBraided[==>, -->, P, TC0] {val a1 = a1; val a2 = a2}

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
  object ProdcatCartesian:
    def apply[==>[_,_], -->[_,_], P[_,_], TC0[_], I](using
      a1: Cartesian.Aux[==>, P, TC0, I],
      a2: Cartesian.Aux[-->, P, TC0, I],
    ): Cartesian.Aux[Prodcat[==>, -->, *, *], P, TC0, I] =
      new ProdcatCartesian[==>, -->, P, TC0, I] {val a1 = a1; val a2 = a2}

  trait ProdcatDistributive[==>[_,_], -->[_,_], P[_,_], PI, S[_,_], SI, TC0[_]]
    extends ProdcatSubcat[==>, -->, TC0]
    with Distributive[Prodcat[==>, -->, *, *], P, S]
  {
    protected def s1: Distributive.Aux[==>, TC0, P, PI, S, SI]
    protected def s2: Distributive.Aux[-->, TC0, P, PI, S, SI]
    type ProductId = PI
    type SumId = SI
    def cartesian: Cartesian.Aux[Prodcat[==>, -->, *, *], P, TC0, PI] =
      ProdcatCartesian[==>, -->, P, TC0, PI](using s1.cartesian, s2.cartesian)
    def cocartesian: Cocartesian.Aux[Prodcat[==>, -->, *, *], S, TC0, SI] =
        ProdcatCartesian(using s1.cocartesian, s2.cocartesian) |>
          Prodcat.traverseDualEq[==>, -->].subst[[f[_,_]] =>> Cartesian.Aux[f[_,_], S, TC0, SI]]
    def distribute[A: TC, B: TC, C: TC] = (s1.distribute, s2.distribute)
  }
  object ProdcatDistributive:
    def apply[==>[_,_], -->[_,_], P[_,_], PI, S[_,_], SI, TC0[_]](using
      s1: Distributive.Aux[==>, TC0, P, PI, S, SI],
      s2: Distributive.Aux[-->, TC0, P, PI, S, SI],
    ): Distributive.Aux[Prodcat[==>, -->, *, *], TC0, P, PI, S, SI] =
      new ProdcatDistributive[==>, -->, P, PI, S, SI, TC0] {val s1 = s1; val s2 = s2}

  trait ProdcatCcc[==>[_,_], -->[_,_], TC0[_], P[_,_], PI, E[_,_]]
    extends ProdcatCartesian[==>, -->, P, TC0, PI]
    with Ccc[Prodcat[==>, -->, *, *], P]
  {
    protected def a1: Ccc.Aux[==>, P, TC0, PI, E]
    protected def a2: Ccc.Aux[-->, P, TC0, PI, E]
    type |->[a, b] = E[a, b]
    def uncurry[A, B, C](f: (A ==> (B |-> C), A --> (B |-> C))) = (a1.uncurry[A, B, C](f._1), a2.uncurry[A, B, C](f._2))
    def curry[A, B, C](f: (P[A, B] ==> C, P[A, B] --> C)) = (a1.curry(f._1), a2.curry(f._2))
  }
  object ProdcatCcc:
    def apply[==>[_,_], -->[_,_], TC0[_], P[_,_], PI, E[_,_]](using
      c1: Ccc.Aux[==>, P, TC0, PI, E],
      c2: Ccc.Aux[-->, P, TC0, PI, E],
    ): Ccc.Aux[Prodcat[==>, -->, *, *], P, TC0, PI, E] =
      new ProdcatCcc[==>, -->, TC0, P, PI, E] {val a1 = c1; val a2 = c2}

  trait ProdcatGroupoid[==>[_,_], -->[_,_], TC0[_]]
    extends ProdcatSubcat[==>, -->, TC0]
    with Groupoid[Prodcat[==>, -->, *, *]]
  {
    protected def s1: Groupoid.Aux[==>, TC0]
    protected def s2: Groupoid.Aux[-->, TC0]
    def flip[A, B](f: (A ==> B, A --> B)) = (s1.flip(f._1), s2.flip(f._2))
  }
  object ProdcatGroupoid:
    def apply[==>[_,_], -->[_,_], TC0[_]](using
      s1: Groupoid.Aux[==>, TC0],
      s2: Groupoid.Aux[-->, TC0],
    ): Groupoid.Aux[Prodcat[==>, -->, *, *], TC0] =
      new ProdcatGroupoid[==>, -->, TC0] {val s1 = s1; val s2 = s2}

  trait ProdcatInit[==>[_,_], -->[_,_], C[_], Init]
    extends Initial[Prodcat[==>, -->, *, *]]
  {
    protected def s1: Initial.Aux[==>, C, Init]
    protected def s2: Initial.Aux[-->, C, Init]
    type I = Init
    type TC[a] = C[a]
    def TC: C[Init] = s1.TC
    def subcat: Subcat.Aux[Prodcat[==>, -->, *, *], C] = ProdcatSubcat[==>, -->, C](using s1.subcat, s2.subcat)
    def initiate[A](using A: TC[A]): (Init ==> A, Init --> A) = (s1.initiate, s2.initiate)
  }
  object ProdcatInit:
    def apply[==>[_,_], -->[_,_], C[_], I](using
      s1: Initial.Aux[==>, C, I],
      s2: Initial.Aux[-->, C, I],
    ): Initial.Aux[Prodcat[==>, -->, *, *], C, I] =
      new ProdcatInit[==>, -->, C, I] {val s1 = s1; val s2 = s2}

  trait ProdcatTerm[==>[_,_], -->[_,_], C[_], T]
    extends Terminal.Proto[Prodcat[==>, -->, *, *], C, T]
  {
    protected def s1: Terminal.Aux[==>, C, T]
    protected def s2: Terminal.Aux[-->, C, T]
    def TC = s1.TC
    override def subcat: Subcat.Aux[Dual[Prodcat[==>, -->, *, *], *, *], C] =
      ProdcatSubcat(using s1.subcat, s2.subcat)
        |> Prodcat.traverseDualEq[==>, -->].subst[[f[_,_]] =>> Subcat.Aux[f, C]]
    def terminate[A](using A: TC[A]): (A ==> T, A --> T) = (s1.terminate, s2.terminate)
  }
  object ProdcatTerm:
    def apply[==>[_,_], -->[_,_], C[_], T](using
      s1: Terminal.Aux[==>, C, T],
      s2: Terminal.Aux[-->, C, T],
    ): Terminal.Aux[Prodcat[==>, -->, *, *], C, T] =
      new ProdcatTerm[==>, -->, C, T] {val s1 = s1; val s2 = s2}


}
