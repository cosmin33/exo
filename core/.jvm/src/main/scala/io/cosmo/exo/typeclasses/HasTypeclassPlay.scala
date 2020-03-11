package io.cosmo.exo.typeclasses

import cats.Functor
import cats.implicits._
import io.cosmo.exo.Iso.HasIso
import io.cosmo.exo.categories.Trivial
import io.cosmo.exo.categories.data.ProdCat.DiCat
import io.cosmo.exo.categories.functors.Exofunctor
import io.cosmo.exo._
import io.cosmo.exo.evidence.{===, =~=}
import io.cosmo.exo.{Iso, ~>, ∀}
import shapeless.the

import scala.language.reflectiveCalls

object HasTypeclassPlay {

  def main(args: Array[String]): Unit = {
    val ltov = ∀.mk[List ~> Vector].from(_.toVector)
    val vtol = ∀.mk[Vector ~> List].from(_.toList)

    val ll: FunK[TypeF[List], TypeF[Vector]] = FunK(ltov)

    println(ltov[Int](List(1, 2)))
    println(ll(List(3, 4)))

    implicit val iso: Iso[FunK, TypeF[List], TypeF[Vector]] =
      Iso.unsafe(FunK(ltov), FunK(vtol))

    val rr1 = the[Iso[FunK, TypeF[List], TypeF[Vector]]]
    val rr2 = the[HasIso[FunK, TypeF[Vector], TypeF[List]]]
    val bb1 = the[HasIso[FunK, TypeF[List], TypeF[Vector]]]

    val ii = iso.chain[TypeF[List]].chain[TypeF[Vector]]
    println(ii.to(List(5, 6)))

    val jj = iso.chainK[List].chainK[Vector]
    println(jj.to(List(7, 8)))

    Functor[List]
    HasTc[Functor, TypeF[List]]

    implicit def funcList1: Exofunctor[Iso[FunK, *, *], * => *, HasTc[Functor, *]] =
      new Exofunctor[Iso[FunK, *, *], * => *, HasTc[Functor, *]] {
        def C = implicitly
        def D = implicitly
        def map[A, B](f: Iso[FunK, A, B]): HasTc[Functor, A] => HasTc[Functor, B] = { ha =>
          val ab: FunK[A, B] = f.to
          val ba: FunK[B, A] = f.from

          val eet: TypeF[ha.F] === TypeF[ab.TypeA] = ha.leibniz.andThen(ab.eqA.flip)

          val fun1: Functor[ab.TypeA] = TypeF.injectivity(eet).subst(ha.instance)

          val u1: ba.TypeA =~= ab.TypeB = TypeF.injectivity(ba.eqA.andThen(ab.eqB.flip))
          val u2: ba.TypeB =~= ab.TypeA = TypeF.injectivity(ba.eqB.andThen(ab.eqA.flip))

          val to:   ab.TypeA ~> ab.TypeB = ab.instance
          val from: ab.TypeB ~> ab.TypeA = u1.lower2[*[_] ~> *[_]](u2)(ba.instance)

          val fff: Functor[ab.TypeB] = new Functor[ab.TypeB] {
            override def map[X, Y](fa: ab.TypeB[X])(f: X => Y) = to[Y](fun1.map(from[X](fa))(f))
          }
          ab.eqB.subst(HasTc.steal(fff))
        }
      }

    def derivationFunctor[TC[_[_]], F[_], G[_]](ab: F <~> G): TC[F] => TC[G] = ???

    val funcVector: HasTc[Functor, TypeF[Vector]] = iso.deriveK[Functor]

    val fv: Functor[Vector] = HasTc.isoCanonic[Functor, Vector].from(funcVector)

    val nv = fv.map(Vector(1, 2))((i: Int) => i * 3)
    println(s"new vector: $nv")

    println("done 1")

    val bbr: FunK[TypeF[List], TypeF[Vector]] = FunK.isoCanonic.flip(ltov)
    val bba: List ~> Vector = bbr.unwrap
    println(s"blah: ${bba.apply(List(5,5,5))}")

    println("done 2")

  }


}
