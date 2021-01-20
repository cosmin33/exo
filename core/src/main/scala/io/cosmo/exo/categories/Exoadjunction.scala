package io.cosmo.exo.categories

import io.cosmo.exo.<=>
import io.cosmo.exo.categories.functors.{Exo, Exomonad}

trait Exoadjunction[==>[_,_], -->[_,_], F[_], G[_]] {
  val subL: Subcat[==>]
  val subR: Subcat[-->]
  def F: Exo[-->, ==>, F]
  def G: Exo[==>, -->, G]

  def isoAdjunction[A, B]: (F[A] ==> B) <=> (A --> G[B])

  def unit  [A](implicit ta: subL.TC[F[A]]): A --> G[F[A]] = isoAdjunction[A, F[A]].to(subL.id[F[A]])
  def counit[A](implicit tb: subR.TC[G[A]]): F[G[A]] ==> A = isoAdjunction[G[A], A].from(subR.id[G[A]])

  def monad1 = new Exomonad[-->, λ[a => subL.TC[F[a]]], λ[a => G[F[a]]]] {
    def pure[A](implicit i: subL.TC[F[A]]) = unit[A]
    def bind[A, B](f: A --> G[F[B]]): G[F[A]] --> G[F[B]] = G.map(isoAdjunction.from(f))
    def map [A, B](f: A --> B): G[F[A]] --> G[F[B]] = G.map(F.map(f))
  }

  def comonad1 = new Exomonad[Dual[==>,*,*], λ[a => subR.TC[G[a]]], λ[a => F[G[a]]]] {
    def pure[A](implicit i: subR.TC[G[A]]) = Dual(counit[A])
    def bind[A, B](f: Dual[==>, A, F[G[B]]]): Dual[==>, F[G[A]], F[G[B]]] = Dual(F.map(isoAdjunction.to(f.toFn)))
    def map[A, B](f: Dual[==>, A, B]): Dual[==>, F[G[A]], F[G[B]]] = Dual(F.map(G.map(f)))
  }


}
