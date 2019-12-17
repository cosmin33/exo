package io.cosmo.exo.categories.functors

trait Pointed[->[_,_], F[_]] extends Endofunctor.ProtoA[->, F] {
  def point[A](implicit A: TC1[A], FA: TC1[F[A]]): A -> F[A]
}

object Pointed {
  type Aux[->[_,_], C[_], F[_]] = Pointed[->, F] {
    type TC1[a] = C[a]; type TC2[a] = C[a]
  }
}
