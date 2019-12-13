package io.cosmo.exo.categories

import io.cosmo.exo.IofModule.Iof
import io.cosmo.exo._
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.evidence.{</<, <~<, =!=, ===, =~=, >~>, Inhabited, Proposition}
import shapeless.{Refute, the}

object CategPlay {

  trait SemicategClass[->[_, _]] {
    final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
    def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C
  }
  object SemicategClass {

    implicit def mapSemicateg: Semicateg[Map] = IofModule.instOf[Any](
      new SemicategClass[Map] {
        override def andThen[A, B, C](ab: Map[A, B], bc: Map[B, C]): Map[A, C] =
          ab.flatMap { case (a, b) => bc.get(b).map(c => (a, c)) }
      })

    implicit def catFn1: Categ.Aux[* => *, Trivial.T1] =
      IofModule.instOf[Categ.AnyBound](new CategClass[* => *] {
        override type TC[a] = Trivial.T1[a]
        override def id[A](implicit A: TC[A]) = identity
        override def andThen[A, B, C](ab: A => B, bc: B => C) = ab.andThen(bc)
      })

    // conversions... //
    implicit def conv1[->[_,_]](implicit C: Categ[->]): Semicateg[->] = IofModule.instOf[Any](C)
    implicit def conv2[->[_,_], C[_]](implicit C: Categ.Aux[->, C]): Categ[->] = IofModule.instOf[Any](C)
  }

  type Semicateg[->[_,_]] = IofModule.Iof[Any, SemicategClass[->]]
  object Semicateg {
    def apply[->[_,_]](implicit S: Semicateg[->]): Semicateg[->] = S
  }

  trait CategClass[->[_, _]] extends SemicategClass[->] {
    type TC[_]
    def id[A](implicit A: TC[A]): A -> A
  }
  object CategClass {
    type Aux[->[_,_], TC0[_]] = CategClass[->] { type TC[ᵒ] = TC0[ᵒ] }

    trait Proto[->[_, _], TC0[_]] extends CategClass[->] { type TC[ᵒ] = TC0[ᵒ] }
  }

  type Categ[->[_,_]] = IofModule.Iof[Any, CategClass[->]]
  object Categ {
    type AnyBound = Any {type TC[_]}
    def apply[->[_,_]](implicit C: Categ[->]): Categ.Aux[->, C.TC] = IofModule.instOf[AnyBound](C)
    type Aux[->[_,_], T[_]] = IofModule.Iof[AnyBound, CategClass.Aux[->, T]]
    type AuxT[->[_,_]] = Aux[->, Trivial.T1]

    // tre'sa mearga asta, altfel solutia cu IofModule nu e ok
    //val bluh: Aux[Function, Trivial.T1] = Categ[* => *]

    implicitly[Semicateg[Map]]
    type C0 = Categ[* => *]
    type CT = Categ.Aux[* => *, Trivial.T1]
    implicitly[CategClass.Aux[* => *, Trivial.T1] <~< CategClass[* => *]]
    implicitly[C0]
    implicitly[CT]
    //implicitly[CT <~< C0]
    //val xsd: CT <~< C0 = InstOfModule.

    the[CategClass.Aux[* => *, Trivial.T1] <~< CategClass[* => *]]
    //the[CategClass.Aux[* => *, Trivial.T1] </< CategClass[* => *]]
    //the[CategClass.Aux[* => *, Trivial.T1] =!= CategClass[* => *]]

    the[CategClass.Aux[* => *, Trivial.T1] <~< CategClass[* => *]]


//    val rr1: Categ.Aux[* => *, Trivial.T1] <~< Categ[* => *] = implicitly[Categ.Aux[* => *, Trivial.T1] <~< Categ[* => *]]
    val rr2: Proposition[Categ.Aux[* => *, Trivial.T1] <~< Categ[* => *]] =
      implicitly[Proposition[Categ.Aux[* => *, Trivial.T1] <~< Categ[* => *]]]
    val rr3: Inhabited[Categ.Aux[* => *, Trivial.T1] <~< Categ[* => *]] =
      Inhabited.witness(_(IofModule.map[Any {type TC[_]}, Any](<~<[CategClass.Aux[* => *, Trivial.T1], CategClass[* => *]])))

    val rr: Categ.Aux[* => *, Trivial.T1] <~< Categ[* => *] =
      IofModule.covary[Any {type TC[_]}, CategClass.Aux[* => *, Trivial.T1], Any, CategClass[* => *]]


    def testfn[->[_,_], A, C[_]](f: A -> A)(implicit C: Categ.Aux[->, C]): Categ.Aux[->, C] = C
    val ff = testfn((i: Int) => i)
    val gg: Aux[Function, Trivial.T1] = ff


  }


  the[Categ[* => *]]
  the[Categ.Aux[* => *, Trivial.T1]]
  the[Categ.AuxT[* => *]]
  val s = the[Semicateg[* => *]]
  the[Semicateg[Map]]

  val c = Categ[* => *]


}
