package io.cosmo.exo.categories


import cats.Functor
import cats.data.OptionT
import cats.implicits._
import io.cosmo.exo.evidence.<~<
import io.cosmo.exo.syntax._
import io.cosmo.exo.typeclasses.{HasTc, TypeK}
import io.cosmo.exo.{<=>, <~>, Iso, IsoFunK, ~>, ∀}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
//import shapeless.Refute
import io.cosmo.exo.categories.functors._

class FunctorsTests  extends AnyFunSuite with Matchers {

  type Tr[x] = Trivial.T1[x]

  implicitly[Endofunctor[<~<, List]] // covariant
  implicitly[Endofunctor[<~<, λ[a => 1]]] // constant

  import io.cosmo.exo.categories.conversions.CatsInstances._

  // IsoFunctorK syntax + typeclass derivation test
  implicit val ilv: List <~> Vector = ∀.mk[List <~> Vector].from(Iso.unsafe(_.toVector, _.toList))
  val fv1: Functor[Vector] = Functor[List].imapK(ilv)
  val fv2: Functor[Vector] = IsoFunK(ilv).deriveK[Functor]
  val fv3: Functor[Vector] = Functor[List].deriveK[Vector]
  assert(fv1.map(Vector(1, 2))(i => i + i).eqv(Vector(2, 4)))
  assert(fv2.map(Vector(1))(_.toString).eqv(Vector("1")))

  // FunctorK syntax test
  val ot: OptionT[List, Int] = OptionT(List(1.some))
  val ov: OptionT[Vector, Int] = FunctorK[OptionT[*[_], Int]].mapK(ilv.to)(ot)
  type O[F[_]] = OptionT[F, Int]
  val ov1: OptionT[Vector, Int] = (ot: O[List]).emapK(ilv.to)
  assert(ov1.eqv(OptionT(Vector(1.some))))

//  def ffo[F[_], A,
//    EF <: Exofunctor[* => *, * => *, F] {type TC1[_]; type TC2[_]},
//    C1[_],
//    C2[_],
//  ](fa: F[A])(implicit
//    FS: SingleOf[Exofunctor[* => *, * => *, F], EF],
//    efef: EF <~< Exofunctor[* => *, * => *, F],
//    //F: EF,
//    C1: EF#TC1 =~= C1,
//    C2: EF#TC2 =~= C2,
//    tt1: C1 =~= Trivial.T1,
//    tt2: C2 =~= Trivial.T1,
//    ee: C1 =~= C2
//  ): Exofunctor.Aux[Function1, Function1, F, Trivial.T1, Trivial.T1] = {
//    //val fff: Exofunctor[Function, Function, F] = efef(F)
//    val cc1: EF#TC1 =~= T1 = C1.andThen(tt1)
//    val cc2: EF#TC2 =~= T1 = C2.andThen(tt2)
//    val ee: Exofunctor.Aux[Function1, Function1, F, EF#TC1, EF#TC2] === Exofunctor.Aux[Function1, Function1, F, T1, T1] =
//      cc1.lower2[Exofunctor.Aux[Function1, Function1, F, *[_], *[_]]](cc2)
//    // impossible
//    ???
//  }

  //val f2: Exofunctor.Aux[Function, T1, Function, T1, List] = ffo(List(1))

//  def ffa[F[_], A,
//    Fs <: {type TC1[_]; type TC2[_]},
//    C1[_],
//    C2[_],
//  ](fa: F[A])(implicit
//    FS: Exofunctor.SingleOf[Endofunctor[Function1, F], Fs],
//    C1: Fs#TC1 =~= C1,
//    C2: Fs#TC2 =~= C2,
//  ): Exofunctor.Aux[Function1, Function1, F, C1, C2] = {
//    val r1 = C1.lower2[Exofunctor.Aux[Function1, Function1, F, *[_], *[_]]](C2)
//    r1(FS.widen)
//  }
//
//  val f3: Exofunctor.Aux[Function, Function, List, T1, T1] = ffa(List(1))
//
//  def ffu[F[_], A,
//    Fs <: {type TC1[_]; type TC2[_]},
//  ](fa: F[A])(implicit
//    FS: Exofunctor.SingleOf[Endofunctor[Function1, F], Fs],
//  ): Exofunctor.Aux[Function1, Function1, F, Fs#TC1, Fs#TC2] = FS.widen
//
//  val f4: Exofunctor.Aux[Function, Function, List, Trivial.T1, Trivial.T1] = ffu(List(1))
//  val f5 = ffu(List(1))




  implicitly[Exo.CovF[List]]
  implicitly[Endofunctor[* => *, List]]

  implicitly[Endobifunctor[* => *, Tuple2]]
  implicitly[Endobifunctor[* => *, Either]]
  implicitly[Endobifunctor[* <=> *, Tuple2]]
  implicitly[Endobifunctor[* <=> *, Either]]

  val F: Exo.CovF[List] = implicitly[Exo.CovF[List]]
  assert(F.map((a: Int) => a * 2)(List(1, 2, 3)) == List(2, 4, 6))


}
