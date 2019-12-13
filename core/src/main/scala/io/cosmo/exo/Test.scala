package io.cosmo.exo

import cats._

object Test {

  //type BF[+TC] = BoxFactory.Facade

//  object funT extends BoxFactory {
//    type Value = List[Option[Int]]
//    type Facade <: OptionT[List, Int]
//  }

  type ≈> [A1[_[_]], A2[_[_]]]           = ∀~[λ[f[_] => A1[f] => A2[f]]]
  object ≈> {
    type Proto[A1[_[_]], A2[_[_]]] = ForallK.Prototype[λ[f[_] => A1[f] => A2[f]]]
  }
  type ≈:>[TC[_[_]], A1[_[_]], A2[_[_]]] = ∀~[λ[f[_] => (TC[f], A1[f]) => A2[f]]]

  trait Nat[A1[_[_]], A2[_[_]]] {
    def fun[F[_]](a1: A1[F]): A2[F]
  }

  val m: Monad[List] = ???
  val f: cats.Functor[List] = m

  val nat: Monad ≈> cats.Functor = ForallK.from(
    new ForallK.Prototype[λ[f[_] => Monad[f] => cats.Functor[f]]] {
      override def apply[F[_]]: Monad[F] => cats.Functor[F] = (m: Monad[F]) => m
    }
  )

  val nat1: Monad ≈> cats.Functor =
    ∀~.from[λ[f[_] => Monad[f] => cats.Functor[f]]](
      ν[∀~.Prototype[λ[f[_] => Monad[f] => cats.Functor[f]]]].apply[F[_]]((m: Monad[F]) => m))

  val nat2: Monad ≈> cats.Functor = ν[≈>.Proto[Monad, cats.Functor]][F[_]](m => m).make

  type Blah[F[_], G[_]] = ∀[λ[a => F[a] => G[a]]]
  object Blah {
    type Proto[F[_], G[_]] = Forall.Prototype[λ[a => F[a] => G[a]]]
//    def unapply[f[_], G[_]]: { type FF[a] = f[a]; type GG[a] = G[a] } =
//      new Unapply[∀∀~[Ci]] { type Bi[f[_], G[_]] = Ci[f, G] }
  }
  val asfd = ν[Blah.Proto[List, Option]].apply[a](_.headOption)


//  // sample from scalaz git hist
//  //val emptyMap: ∀∀[λ[(α, β) => Map[α, β]]] =
//  type ~~>[f[_, _], G[_, _]] = ∀∀[λ[(α, β) => f[α, β] => G[α, β]]]
//  type Option2[TC, B] = Option[(TC, B)]
//  val pick: Map ~~> Option2 = ∀∀.mk[Map ~~> Option2].from(_.headOption)
//  assert( pick[String, Int](Map("hi" -> 5)) == Some("hi" -> 5) )
//
//  // extra syntax for applying a binatural transformation to univarsally quantified value
//  implicit class BinaturalTransformationOps[f[_, _], G[_, _]](trans: f ~~> G) {
//    def $(f: ∀∀[f]): ∀∀[G] = ∀∀.of[G](trans.apply.apply(f.apply))
//  }
//  // applying a universally quantified function to a universally quantified value
//  // yields a universally quantified value
//  //val none2: ∀∀[Option2] = pick $ emptyMap

}
