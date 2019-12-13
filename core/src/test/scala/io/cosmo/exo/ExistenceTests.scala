package io.cosmo.exo

import cats.Id
import cats.data.Kleisli
import io.cosmo.exo.ExistenceHelpers.K211Mod
import io.cosmo.exo.evidence.===
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite


class ExistenceTests extends AnyFunSuite with Matchers {

  test("blah") {
    val kl: Kleisli[Option, Int, String] = Kleisli((i: Int) => Option(i.toString + " !!"))

    val r1 = kl.run(5)
    println(r1)

    val e1: ExistsK211[Kleisli] = ExistsK211[Kleisli](kl)
    val er1: ExistsK211[Kleisli] = ExistsK211.apply(kl)

    def fff[x](implicit i: x <:< List[Int]): x <:< List[Int] = implicitly[x <:< List[Int]]
    fff[List[Int]]
    //Sigma.summon[λ[x => x <:< List[Int]]](Nil)

    //implicitly[Kleisli[Option, Int, String] === er1.]

//    def iaca(k: ExistsK211[Kleisli])(implicit xx: k.A === Int, x2: k.B === String): Int = 0
//    iaca(e1)

    //val re1: Kleisli[Option, Int, String] = er1.value
    //val re2: Kleisli[List, Int, String] = e1.value

    val re5 = er1.value

    val e2 = ∃(Nil: List[Int])
    //val re2 = ∃.

    //val rhf2 = re1.run(5)


  }

  class Foo[A](val value: A) {
    def show(a: A): String = a.toString
  }

  test("constructors") {
    val f1: ∃[Foo] = ∃(new Foo(1))
    val f2: ∃[Foo] = ∃(new Foo(1))
    val f3: ∃[Foo] = ∃(new Foo(1))

    val x1 = f1.value.show(f1.value.value)
    x1 should be ("1")

    val x2 = f1 match {
      case ExistsK1(f) => f.show(f.value)
    }
    x2 should be ("1")

    val x3 = {
      val x = f1.value
      x.show(x.value)
    }
    x3 should be ("1")
  }

  test("allocation-less") {
    val f1: ∃[Foo] = ∃(new Foo(1))
    f1.getClass should be (classOf[Foo[_]])

    val f2: ∃[Id] = ∃.apply[Id, Int](1: Int)
    val fq2: ∃[Id] = ∃[Id].apply(1: Int)
    val fr2: ∃[Id] = ∃[Id](1: Int)

//    fq2.getClass should be (classOf[java.lang.Integer])
//    f2.getClass should be (classOf[java.lang.Integer])

    val f3 = ∃[λ[X => Int], Int](1)
    val fq3 = ∃[λ[X => Int]].apply(1)
    val fr3 = ∃[λ[X => Int]](1)
//    f3.getClass should be (classOf[java.lang.Integer])
  }


  /** no ClassTag available for now; implement when needed.. */
//  test("arrays") {
//    val f1: ∃[Array] = ∃(Array[Int](1))
//    f1.getClass should be (classOf[Array[Int]])
//    val a = f1.value(0)
//    a.getClass should be (classOf[java.lang.Integer])
//
//    Array(∃[Option](Some(1)))
//
//    val f2: Array[∃[Id]] = Array(∃[Id](1), ∃[Id]("str"))
//    f2(0) should be (1)
//    f2(1) should be ("str")
//  }

}

