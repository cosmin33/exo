package io.cosmo.exo.evidence

trait IsInjectiveK[A[_[_]]] {

  def apply[F[_], G[_]](implicit ev: A[F] === A[G]): F =~= G

}

