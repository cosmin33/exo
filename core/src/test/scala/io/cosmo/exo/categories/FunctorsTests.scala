package io.cosmo.exo.categories


import cats.{Functor, Id}
import cats.implicits._
import io.cosmo.exo.{Pi, SingleOf}
import io.cosmo.exo.categories.Subcat.Aux
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.evidence.{<~<, ===, =~=, IsK}
import io.cosmo.exo.typeclasses.TypeF
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
//import shapeless.Refute
import io.cosmo.exo.categories.functors._

class FunctorsTests  extends AnyFunSuite with Matchers {

  type Tr[x] = Trivial.T1[x]

  implicitly[Endofunctor.AuxT[<~<, List]] // covariant
  implicitly[Endofunctor.AuxT[<~<, λ[a => 1]]] // constant

  import io.cosmo.exo.categories.conversions.CatsInstances._

  def ffo[F[_], A,
    EF <: Exofunctor[* => *, * => *, F] {type TC1[_]; type TC2[_]},
    C1[_],
    C2[_],
  ](fa: F[A])(implicit
    FS: SingleOf[Exofunctor[* => *, * => *, F], EF],
    efef: EF <~< Exofunctor[* => *, * => *, F],
    //F: EF,
    C1: EF#TC1 =~= C1,
    C2: EF#TC2 =~= C2,
    tt1: C1 =~= Trivial.T1,
    tt2: C2 =~= Trivial.T1,
    ee: C1 =~= C2
  ): Exofunctor.Aux[Function1, Function1, F, Trivial.T1, Trivial.T1] = {
    //val fff: Exofunctor[Function, Function, F] = efef(F)
    val cc1: EF#TC1 =~= T1 = C1.andThen(tt1)
    val cc2: EF#TC2 =~= T1 = C2.andThen(tt2)
    val ee: Exofunctor.Aux[Function1, Function1, F, EF#TC1, EF#TC2] === Exofunctor.Aux[Function1, Function1, F, T1, T1] =
      cc1.lower2[Exofunctor.Aux[Function1, Function1, F, *[_], *[_]]](cc2)
    // impossible
    ???
  }

  //val f2: Exofunctor.Aux[Function, T1, Function, T1, List] = ffo(List(1))

  def ffa[F[_], A,
    Fs <: {type TC1[_]; type TC2[_]},
    C1[_],
    C2[_],
  ](fa: F[A])(implicit
    FS: Exofunctor.SingleOf[Endofunctor[Function1, F], Fs],
    C1: Fs#TC1 =~= C1,
    C2: Fs#TC2 =~= C2,
  ): Exofunctor.Aux[Function1, Function1, F, C1, C2] = {
    val r1 = C1.lower2[Exofunctor.Aux[Function1, Function1, F, *[_], *[_]]](C2)
    r1(FS.widen)
  }

  val f3: Exofunctor.Aux[Function, Function, List, T1, T1] = ffa(List(1))

  def ffu[F[_], A,
    Fs <: {type TC1[_]; type TC2[_]},
  ](fa: F[A])(implicit
    FS: Exofunctor.SingleOf[Endofunctor[Function1, F], Fs],
  ): Exofunctor.Aux[Function1, Function1, F, Fs#TC1, Fs#TC2] = FS.widen

  val f4: Exofunctor.Aux[Function, Function, List, Trivial.T1, Trivial.T1] = ffu(List(1))
  val f5 = ffu(List(1))




  val saf: Endofunctor.CovF[List] = endofunctor3functor[List]
  implicitly[Functor[List]]
  implicitly[Endofunctor.CovF[List]]
  implicitly[Endofunctor[* => *, List]]
  implicitly[Exofunctor[* => *, * => *, List]]
  implicitly[Exofunctor.Aux[* => *, * => *, List, Tr, Tr]]

  implicitly[Endobifunctor.Aux[* => *, Tr, Tuple2]]
  implicitly[Exobifunctor.Aux[* => *, Tr, * => *, Tr, * => *, Tr, Tuple2]]
  implicitly[Endobifunctor.Aux[* => *, Tr, Either]]
  implicitly[Exobifunctor.Aux[* => *, Tr, * => *, Tr, * => *, Tr, Either]]

//  implicitly[Endobifunctor[* => *, Tuple2]]
  //implicitly[Endobifunctor[* => *, Either]]





}

object Iaca {
  // A couple of type classes with type members ...
  trait Foo[T] {
    type A
  }

  object Foo {
    implicit val fooIS = new Foo[Int] { type A = String }
  }

  trait Bar[T] {
    type B
    val value: B
  }

  object Bar {
    implicit val barSB = new Bar[String] {
      type B = Boolean
      val value = true
    }
  }

  // What we want to write ...
  //
  //  def run[T](t: T)(implicit foo: Foo[T], bar: Bar[foo.A]): bar.B = bar.value
  //
  // or maybe ...
  //
  //  def run[T](t: T)(implicit foo: Foo[T])(implicit bar: Bar[foo.A]): bar.B = bar.value
  //
  // but can't ... in the first case the compiler complains about a dependent type (foo.A)
  // appearing in the same parameter block as its prefix (foo); in the second the compiler
  // chokes on the multiple implicit parameter blocks.

  // But we can encode the above with the help of singleton types ...

  // SingletonOf[T, U] represents an implicit value of type T narrowed to its
  // singleton type U.
  case class SingletonOf[T, U](value: U)
  object SingletonOf {
    implicit def mkSingletonOf[T <: AnyRef](implicit t: T): SingletonOf[T, t.type] = SingletonOf(t)
  }

  // The implicit resolution of SingletonOf[Foo[T], fooT] will result in the type
  // fooT being inferred as the singleton type of the in-scope Foo[T] value.
  // We then rely on the equivalence between,
  //
  //   foo.A
  //
  // and,
  //
  //   foo.type#A
  //
  // to rewrite the problematic dependently chained parameter block to a form
  // that scalac is happy to digest ...
  def run[T, fooT <: { type A }](t: T)
    (implicit sFoo: SingletonOf[Foo[T], fooT], bar: Bar[fooT#A]): bar.B = bar.value

  val value = run(23)
  assert(value: Boolean)
}