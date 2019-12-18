package io.cosmo.exo

import cats.data.Kleisli
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.categories.{Cartesian, Ccc, HasTerminalObject}
import io.cosmo.exo.evidence.Inhabited
import io.cosmo.exo.syntax._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ForallSomeTests extends AnyFunSuite with Matchers {
  class Foo[A]

  test("constructors") {

    val it /*: ∀[λ[x => Inhabited[Int]]]*/ = Forall.of[λ[x => Inhabited[Int]]].from(implicitly)

    val f1: ∀[Foo] = ∀.of(new Foo)
    val f2: ∀[Foo] = Forall.of(new Foo)
    val f3: ∀[Foo] = Forall.of[Foo].from(new Foo)
    val f4: ∀[Foo] = Forall.of[Foo].from(new Foo)
    val f5: ∀[Foo] = Forall.from(new ∀.Prototype[Foo] {
      override def apply[X]: Foo[X] = new Foo
    })
    val f7 = ∀.of[Foo].from(new Foo)
    val f10 = Forall.of[Foo].from(new Foo)
    val f11 = Forall.from(new Forall.Prototype[Foo] {
      override def apply[X]: Foo[X] = new Foo
    })

    def rr[F[_], K, V](key: K): F[V] = ???
    val rrr: ForallK11[λ[(f[_],k,v) => k => f[v]]] = ForallK11.of[λ[(f[_],k,v) => k => f[v]]].from(rr)

  }

  test("forall stuff...") {
    type ~>[F[_], G[_]] = ∀[λ[a => F[a] => G[a]]]
    type T[a] = List[a] => Option[a]
    type W = Forall[λ[a => List[a] => Option[a]]]
    val nil: ∀[List] =  ∀.of[List].from(Nil)
    val nn1: List[Int] = nil.of[Int]
    val nn2: List[Int] = nil[Int]



    val w1: List ~> Option =  Forall.mk[List ~> Option].from(a => a.headOption)
    val s2: W = Forall.of[T].from(a => a.headOption)

  }

  test("exists stuff...") {
    type Kl[F[_], K, V] = Kleisli[F, K, V]
    val kl: Kleisli[Option, Int, String] = Kleisli((i: Int) => Option(i.toString + " !!"))
    val l: List[Int] = List(1, 2)
    val ekl: ∃[List] = ∃[List].apply(l)
    val jr: List[ekl.A] = ExistsK1.unwrap(ekl)
    assert(l == jr)
    assert(l eq jr)
  }

  test("exists allocation-less") {
    val f1: ∀[Foo] = ∀.of(new Foo)
    f1.getClass should be (classOf[Foo[_]])

    println("'testing...")

    val f2 = ∀.of[λ[X => Int]].from(1)
    // TODO: this works only in java; find a way to cross..
    //f2.getClass should be (classOf[java.lang.Integer])

  }

  test("arrays") {
    //val f1: Array[∀[Foo]] = Array(∀.of[Foo](new Foo))
  }

}
