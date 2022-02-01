package io.cosmo.exo.categories

import io.cosmo.exo.<=>
import io.cosmo.exo.categories.data.Derive
import io.cosmo.exo.categories.functors.Exo

trait Exoadjunction[==>[_,_], -->[_,_], F[_], G[_]] {
  val subL: Subcat[==>]
  val subR: Subcat[-->]
  def F: Exo[-->, ==>, F]
  def G: Exo[==>, -->, G]

  def iso[A, B]: (F[A] ==> B) <=> (A --> G[B])

  def unit  [A](implicit t: subL.TC[F[A]]): A --> G[F[A]] = iso[A, F[A]].to  (subL.id[F[A]])
  def counit[A](implicit t: subR.TC[G[A]]): F[G[A]] ==> A = iso[G[A], A].from(subR.id[G[A]])

  def monad  [A, B]: (A --> G[F[B]]) => (G[F[A]] --> G[F[B]]) = iso[A, F[B]].from andThen G.map[F[A], F[B]]
  def comonad[A, B]: (F[G[A]] ==> B) => (F[G[A]] ==> F[G[B]]) = iso[G[A], B].to   andThen F.map[G[A], G[B]]

  def subcatFG: Subcat.Aux[λ[(a,b) => F[G[a]] ==> b], λ[a => subR.TC[G[a]]]] =
    new Subcat[λ[(a,b) => F[G[a]] ==> b]] {
      type TC[a] = subR.TC[G[a]]
      def id[A: TC]: F[G[A]] ==> A = counit[A]
      def andThen[A, B, C](ab: F[G[A]] ==> B, bc: F[G[B]] ==> C) = subL.andThen(comonad(ab), bc)
    }

  def subcatGF: Subcat.Aux[λ[(a,b) => a --> G[F[b]]], λ[a => subL.TC[F[a]]]] =
    new Subcat[λ[(a,b) => a --> G[F[b]]]] {
      type TC[a] = subL.TC[F[a]]
      def id[A: TC]: A --> G[F[A]] = unit[A]
      def andThen[A, B, C](ab: A --> G[F[B]], bc: B --> G[F[C]]): A --> G[F[C]] = subR.andThen(ab, monad(bc))
    }

  def subcatFG_(implicit d: Derive[G, subR.TC]): Subcat.Aux[λ[(a,b) => F[G[a]] ==> b], subR.TC] =
    new Subcat[λ[(a,b) => F[G[a]] ==> b]] {
      type TC[a] = subR.TC[a]
      def id[A: TC]: F[G[A]] ==> A = counit[A](d.derive)
      def andThen[A, B, C](ab: F[G[A]] ==> B, bc: F[G[B]] ==> C) = subL.andThen(comonad(ab), bc)
    }
  def subcatGF_(implicit d: Derive[F, subL.TC]): Subcat.Aux[λ[(a,b) => a --> G[F[b]]], subL.TC] =
    new Subcat[λ[(a,b) => a --> G[F[b]]]] {
      type TC[a] = subL.TC[a]
      def id[A: TC]: A --> G[F[A]] = unit[A](d.derive)
      def andThen[A, B, C](ab: A --> G[F[B]], bc: B --> G[F[C]]): A --> G[F[C]] = subR.andThen(ab, monad(bc))
    }

}
