package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

trait ExofunctorK2[==>[_,_], -->[_,_], A[_[_,_]]]:
  def map[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] ==> G[a, b]]): A[F] --> A[G]
object ExofunctorK2:
  def apply[==>[_,_], -->[_,_], A[_[_,_]]](using E: ExofunctorK2[==>, -->, A]): ExofunctorK2[==>, -->, A] = E
  def unsafe[==>[_,_], -->[_,_], A[_[_,_]]](fn: [F[_,_], G[_,_]] => ∀∀[[a, b] =>> F[a, b] ==> G[a, b]] => (A[F] --> A[G])): ExofunctorK2[==>, -->, A] =
    new ExofunctorK2[==>, -->, A] { def map[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] ==> G[a, b]]): A[F] --> A[G] = fn[F, G](f) }
