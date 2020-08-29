package io.cosmo.exo.evidence

import io.cosmo.exo.{<=>, Iso, ∀~∀~}

trait IsInjectiveH[A[_[_]]] {

  def apply[F[_], G[_]](implicit ev: A[F] === A[G]): F =~= G

}

object IsInjectiveH {

  type Canonic[A[_[_]]] = ∀~∀~[λ[(f[_],g[_]) => (A[f] === A[g]) => (f =~= g)]]

  implicit def isoCanonic[A[_[_]]]: Canonic[A] <=> IsInjectiveH[A] =
    Iso.unsafe(
      can => new IsInjectiveH[A] { def apply[F[_], G[_]](implicit ev: ===[A[F], A[G]]) = can[F, G](ev) },
      isi => ∀~∀~.mk[Canonic[A]].from(isi.apply(_))
    )

}