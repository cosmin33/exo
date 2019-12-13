package io.cosmo.exo

import cats.implicits._
import io.cosmo.exo.Iso.{Aux, AuxTF, HasIso}
import io.cosmo.exo.categories.Trivial.T1
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
import io.cosmo.exo.categories._
import io.cosmo.exo.evidence._
import io.cosmo.exo.typeclasses.TypeF
import shapeless.{Refute, tag}
import shapeless.tag.@@

class IsoTests extends AnyFunSuite with Matchers {



  case class Int1(i: Int)
  trait Y
  trait Z

  locally {
    implicit val i1: Aux[Function, T1, Int, Int1] = Iso.unsafeT[Int, Int1](Int1, _.i)

    the[<=>[Int, Int1]]
    the[Iso.Aux[* => *, Trivial.T1, Int, Int1]]
    the[Iso.Aux[* => *, Trivial.T1, Int1, Int]]

    implicitly[HasIso[* => *, Int, Int1]]
    implicitly[HasIso[* => *, Int1, Int]]
    implicitly[HasIso.Aux[* => *, Trivial.T1, Int, Int1]]
    implicitly[HasIso.Aux[* => *, Trivial.T1, Int1, Int]]
    val rrr = implicitly[HasIso.Aux[* => *, Trivial.T1, Int1, Int]]

    val iso: Iso[Function, Int, Int1] = Iso[* => *, Int, Int1]


    val it: <=>[Int, Long] = Iso.unsafe((i: Int) => i.toLong, (l: Long) => l.toInt)

    iso.chain[Int].chain[Int].chain[Int].chain[Int1]
    iso.flip.chain[Int1]

    val ii1 = implicitly[Iso.Aux[* => *, Trivial.T1, Int, Int1]]
    ii1.chain[Int]

    implicitly[Refute[Iso[* => *, Int1, Int]]]

    implicit def isoListVect: <~>[List, Vector] = ∀.mk[List <~> Vector].from(Iso.unsafeT(_.toVector, _.toList))
    implicitly[<~>[List, Vector]]


    println("done")
  }

  implicitly[Refute[<=>[Unit, Int]]]
  implicitly[<=>[4, 133]]
  implicitly[<=>[Unit, 55]]
  implicitly[HasIso[* => *, 55, Unit]]
  implicitly[HasIso[* => *, Unit, 55]]
  val ggs: Iso.AuxT[* => *, Unit, 55] = Iso.isoUnitSingleton[55]
  val fgs: Iso.AuxT[* => *, Unit, 55] = implicitly
  val fgg: Iso.Aux[* => *, Trivial.T1, Unit, 55] = implicitly
  val fgh: Iso.Aux[* => *, Trivial.T1, 55, Unit] = implicitly[HasIso.Aux[* => *, Trivial.T1, 55, Unit]]
  val fgr: Iso.Aux[* => *, Trivial.T1, Unit, 55] = implicitly[HasIso.Aux[* => *, Trivial.T1, Unit, 55]]



  the[<=>[Unit, 6]]
  //the[<=>[6, Unit]]

  def sss[A, B](implicit i: HasIso[* => *, A, B]) = i

  sss[6, Unit]


  the[Iso.Aux[Function1, Trivial.T1, 6, Unit]]
  the[Iso.Aux[Function1, Trivial.T1, Unit, 6]]

  case class Afa[A, F[_]](a: A, fa: F[A])
  val tupleIso: Afa[Int, List] <=> (Int, List[Int]) = Iso.forCaseClass[Afa[Int, List]]
  assert(tupleIso.from((1, List(2,3))) == Afa(1, List(2,3)))

}
