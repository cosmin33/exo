package io.cosmo.exo.categories

import io.cosmo.exo.{<=>, Iso}

trait Exoadjunction[==>[_,_], -->[_,_], F[_], G[_]] {
  val subL: Subcat[==>]
  val subR: Subcat[-->]
  def funF: Endofunctor[==>, F]
  def funG: Endofunctor[-->, G]

  def isoAdjunction[A, B]: (F[A] ==> B) <=> (A --> G[B])

  def unit  [A](implicit tb: subR.TC[G[A]]): F[G[A]] ==> A = isoAdjunction[G[A], A].from(subR.id[G[A]])
  def counit[A](implicit ta: subL.TC[F[A]]): A --> G[F[A]] = isoAdjunction[A, F[A]].to(subL.id[F[A]])

  def unit1[A](implicit
    ta: subL.TC[F[A]],
    tb: subR.TC[G[A]]
  ): A <=> F[G[A]] = {
    val s1: F[A] ==> F[A] = subL.id[F[A]]
    val s2: G[A] --> G[A] = subR.id[G[A]]

    val t1: F[G[A]] ==> A <=> (G[A] --> G[A]) = isoAdjunction[G[A], A]
    val t2: F[A] ==> F[A] <=> (A --> G[F[A]]) = isoAdjunction[A, F[A]]

    val mrr1: F[G[A]] ==> A = isoAdjunction[G[A], A].from(subR.id[G[A]])
    val mrr2: A --> G[F[A]] = isoAdjunction[A, F[A]].to(subL.id[F[A]])
    //val t1: F[G[A]] --> A = isoAdjunction[G[A], A].from(subR.id[G[A]])
    //val t2 = isoAdjunction[A, F[A]].to(subL.id[F[A]])
    //val r1: F[A] --> F[A] <=> (A --> G[F[A]]) = isoAdjunction[A, F[A]]

    //isoAdjunction
    ???
  }

}
