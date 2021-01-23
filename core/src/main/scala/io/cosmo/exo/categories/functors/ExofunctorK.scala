package io.cosmo.exo.categories.functors

import cats.Monad
import io.cosmo.exo.evidence.{===, Is}
import io.cosmo.exo.typeclasses.TypeF
import io.cosmo.exo.{<~>, FunK, Iso, ~>, ∀}
import cats.implicits._
import io.cosmo.exo

trait ExofunctorK[==>[_,_], -->[_,_], X[_[_]]] {
  def map[F[_], G[_]](f: ∀[λ[a => F[a] ==> G[a]]]): X[F] --> X[G]
}

trait ExofunctorK1[==>[_,_], -->[_,_], X[_[_],_]] {
  def map[F[_], G[_]](f: ∀[λ[a => F[a] ==> G[a]]]): ∀[λ[a => X[F, a] --> X[G, a]]]
}

trait Magarie[L[_[_]], TF] {
  type F[_]
  def eq: TF === TypeF[F]
  def obj: L[F]
}
object Magarie {
  type Aux[L[_[_]], TF, F0[_]] = Magarie[L, TF] { type F[a] = F0[a] }

  def apply[L[_[_]], F0[_]](l: L[F0]): Magarie[L, TypeF[F0]] =
    new Magarie[L, TypeF[F0]] { type F[a] = F0[a]; val eq = Is.refl; val obj = l }

  val ll: Monad[List] = Monad[List]
  val l1: Magarie[Monad, TypeF[List]] = Magarie(ll)

  def iso: List <~> Vector = ∀.mk[List <~> Vector].from(Iso.unsafe(_.toVector, _.toList))

  def funcTest: Exo[FunK, * => *, Magarie[Monad, *]] =
    new Exo[FunK, * => *, Magarie[Monad, *]] {
      def map[A, B](f: FunK[A, B]): Magarie[Monad, A] => Magarie[Monad, B] = { ma =>
        val ff: f.TypeA ~> f.TypeB = f.fn
        val xx: Monad[ma.F] = ma.obj
        val res = new Magarie[Monad, B] {
          type F[a] = f.TypeB[a]
          def eq: B === TypeF[F] = ???
          def obj: Monad[F] = ???
        }

        ???
      }
    }

}
