package io.cosmo.exo.categories

import io.cosmo.exo.<=>
import io.cosmo.exo.categories.functors.Exo

trait Exoadjunction[==>[_,_], -->[_,_], F[_], G[_]] {
  val subL: Subcat[==>]
  val subR: Subcat[-->]
  def F: Exo[-->, ==>, F]
  def G: Exo[==>, -->, G]

  def isoAdjunction[A, B]: (F[A] ==> B) <=> (A --> G[B])

  def unit  [A](implicit ta: subL.TC[F[A]]): A --> G[F[A]] = isoAdjunction[A, F[A]].to(subL.id[F[A]])
  def counit[A](implicit tb: subR.TC[G[A]]): F[G[A]] ==> A = isoAdjunction[G[A], A].from(subR.id[G[A]])

}
