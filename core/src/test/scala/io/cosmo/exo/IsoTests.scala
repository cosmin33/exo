package io.cosmo.exo

import cats.arrow.Arrow
import cats.data.{AndThen, Ior, Validated}
import cats.{Functor, Order, Semigroup}
import cats.implicits._
import io.cosmo.exo.Iso.HasIso
import io.cosmo.exo.categories.{Distributive, Trivial}
import io.cosmo.exo.categories.conversions.CatsInstances._
import io.cosmo.exo.categories.functors.LaxSemigroupal
import io.cosmo.exo.evidence.internal.Unsafe
import io.cosmo.exo.evidence.{===, =~=, =~~=}
import io.cosmo.exo.typeclasses.TypeF
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import shapeless.Refute

class IsoTests extends AnyFunSuite with Matchers {

  test("chain") {
    // Isomorphisms from categorical constructs
    Iso[String].chain[(String, Unit)].chain[String].chain[(Unit, String)]
    Iso[String].chain[String /\ Unit].chain[String].chain[Unit /\ String]
    Iso[String => Unit].chain[Unit].chain[Int => Unit]
    Iso[Void => String].chain[Unit].chain[Void => Int].chain[Int => Unit]
    Iso[(String => Int, Long => Int)].chain[String \/ Long => Int]
    Iso[(String => Int, String => Long)].chain[String => (Int, Long)]
    Iso[(String, Int)].chain[(Int, String)].chain[Int /\ String]
    //Iso[(String, Int \/ Long)].chain[(String, Int) \/ (String, Long)]
    //Iso[String /\ (Int \/ Long)].chain[(String /\ Int) \/ (String /\ Long)]
    implicitly[Distributive[* => *]]
//    implicitly[Distributive.Aux1[* => *, Trivial.T1, /\, \/]]
//    val xx: Iso[* => *, String /\ (Int \/ Long), (String /\ Int) \/ (String /\ Long)] =
//      Iso.isoDistributive[* => *, /\, \/, String, Int, Long, Trivial.T1]

//    implicit val isoIL: Int <=> Long = Iso.unsafe(_.toLong, _.toInt)
//    implicit val isoSI: String <=> Int = Iso.unsafe(_.toInt, _.toString)
//    assert(Iso[String].chain[Int].chain[Long].flip.chain[String].chain[String].apply(4L) == "4")
  }

  test("Iso syntax") {
    implicit val isoIL: Int <=> Long = Iso.unsafe(_.toLong, _.toInt)
    implicit val isoSI: String <=> Int = Iso.unsafe(_.toInt, _.toString)
    assert(6.isoTo[String] == "6")
  }

  test("derive") {
    implicit val isoIL: Int <=> Long = Iso.unsafe(_.toLong, _.toInt)
    implicit val isoSI: String <=> Int = Iso.unsafe(_.toInt, _.toString)

    isoSI.flip.derive[Semigroup]
    val sl: Semigroup[Long] = isoIL.derive[Semigroup]
    assert(sl.combine(1L, 2L) == 3L)
  }

  test("HasIso implicit search") {
    implicit val isoIL: Int <=> Long = Iso.unsafe(_.toLong, _.toInt)
    implicit val isoSI: String <=> Int = Iso.unsafe(_.toInt, _.toString)

    Iso[String].chain[Int].chain[Long]

    Iso[4].chain[6]

    implicitly[HasIso[* => *, String, Int]]
    implicitly[HasIso[* => *, Int, String]]
    implicitly[HasIso[* => *, Int, Int]]
    implicitly[HasIso[FunK, TypeF[List], TypeF[List]]]
    implicitly[Refute[HasIso[* => *, String, Long]]]

    Iso[Iso[* => *, String, Int]].chain[HasIso[* => *, String, Int]]

    def mrr1[->[_,_], A, B] = implicitly[HasIso[* => *, HasIso[->, A, B], Iso[->, A, B]]]

    // Isomorphisms derived from lifting equality
    type Int1 = InstanceOf[Int]
    type Long1 = InstanceOf[Long]
    type String1 = InstanceOf[String]
    type Double1 = InstanceOf[Double]
    implicit val e1: Int === Int1       = InstanceOf.is
    implicit val e2: Long === Long1     = InstanceOf.is
    implicit val e3: String === String1 = InstanceOf.is
    implicit val e4: Double === Double1 = InstanceOf.is
    // checking Iso equality lift implicits (for types *)
    implicitly[List[Int] <=> List[Int1]]
    implicitly[(Int, Long) <=> (Int1, Long1)]
    implicitly[(Int, Long, String) <=> (Int1, Long1, String1)]
    implicitly[(Int, Long, String, Double) <=> (Int1, Long1, String1, Double1)]

    type List1[a] = Unit
    type Option1[a] = Unit
    type Vector1[a] = Unit
    type Order1[a] = Unit
    implicit val d1: List =~= List1     = Unsafe.isK
    implicit val d2: Option =~= Option1 = Unsafe.isK
    implicit val d3: Vector =~= Vector1 = Unsafe.isK
    implicit val d4: Order =~= Order1   = Unsafe.isK
    case class T2[F[_], G[_]](t1: F[Int], t2: G[Int])
    case class T3[F[_], G[_], H[_]](t1: F[Int], t2: G[Int], t3: H[Int])
    case class T4[F[_], G[_], H[_], I[_]](t1: F[Int], t2: G[Int], t3: H[Int], t4: I[Int])
    // checking Iso equality lift implicits (for kinds *[_])
    implicitly[Functor[List] <=> Functor[List1]]
    implicitly[T2[List, Option] <=> T2[List1, Option1]]
    implicitly[T3[List, Option, Vector] <=> T3[List1, Option1, Vector1]]
    implicitly[T4[List, Option, Vector, Order] <=> T4[List1, Option1, Vector1, Order1]]

    type Validated1[a, b] = Unit
    type Ior1[a, b] = Unit
    type AndThen1[a, b] = Unit
    type Either1[a, b] = Unit
    implicit val f1: Validated =~~= Validated1 = Unsafe.isK2
    implicit val f2: Ior =~~= Ior1 = Unsafe.isK2
    implicit val f3: AndThen =~~= AndThen1 = Unsafe.isK2
    implicit val f4: Either =~~= Either1 = Unsafe.isK2
    case class F2[F[_,_], G[_,_]](t1: F[Int, Int], t2: G[Int, Int])
    case class F3[F[_,_], G[_,_], H[_,_]](t: Int)
    case class F4[F[_,_], G[_,_], H[_,_], I[_,_]](t: Int)
    case class F5[F[_,_], G[_,_], H[_,_], I[_,_], J[_,_]](t: Int)
    // checking Iso equality lift implicits (for kinds *[_,_])
    implicitly[Arrow[Validated] <=> Arrow[Validated1]]
    implicitly[F2[Validated, Ior] <=> F2[Validated1, Ior1]]
    implicitly[F2[Validated, Ior] <=> F2[Validated, Ior1]]
    implicitly[F2[Validated, Ior] <=> F2[Validated1, Ior]]
    implicitly[F3[Validated, Ior, AndThen] <=> F3[Validated1, Ior1, AndThen1]]
    implicitly[F4[Validated, Ior, AndThen, Either] <=> F4[Validated1, Ior1, AndThen1, Either1]]
    Iso.refl[F4[Validated, Ior, AndThen, Either]].chain[F4[Validated1, Ior1, AndThen1, Either1]]
    implicitly[F5[Validated, Ior, AndThen, Either, Either] <=> F5[Validated1, Ior1, AndThen1, Either1, Either]]

  }

  test("case class <-> tupleN iso derivation") {
    case class Afa[A, F[_]](a: A, fa: F[A])
    def tupIso[A, F[_]] = Iso.forCaseClass[Afa[A, F]]
    assert(tupIso.flip.apply((1, List(2, 3))) == Afa(1, List(2, 3)))
  }

  case class Int1(i: Int)
  trait Y
  trait Z

  locally {

    implicit def isoListVect: <~>[List, Vector] = ∀.mk[List <~> Vector].from(Iso.unsafe(_.toVector, _.toList))
    val lv1: List <~> Vector = implicitly[<~>[List, Vector]]

    implicitly[HasIso[FunK, TypeF[List], TypeF[Vector]]]
    implicitly[HasIso[FunK, TypeF[Vector], TypeF[List]]]

    val rrr: HasIso[FunK, TypeF[List], TypeF[Vector]] = implicitly[HasIso[FunK, TypeF[List], TypeF[Vector]]]
    val lv2: List <~> Vector = TypeF[List].isoWith[Vector]

  }

}
