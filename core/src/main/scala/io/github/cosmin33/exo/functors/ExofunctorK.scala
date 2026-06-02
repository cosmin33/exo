package io.github.cosmin33.exo.functors

import io.github.cosmin33.exo.*
import io.github.cosmin33.exo.categories.*
import io.github.cosmin33.exo.evidence.*
import io.github.cosmin33.exo.syntax.*

trait ExofunctorK[==>[_,_], -->[_,_], A[_[_]]]:
  def map[F[_], G[_]](f: ∀[[a] =>> F[a] ==> G[a]]): A[F] --> A[G]
object ExofunctorK:
  def apply[==>[_,_], -->[_,_], A[_[_]]](using E: ExofunctorK[==>, -->, A]): ExofunctorK[==>, -->, A] = E
  def unsafe[==>[_,_], -->[_,_], A[_[_]]](fn: [F[_], G[_]] => ∀[[a] =>> F[a] ==> G[a]] => (A[F] --> A[G])): ExofunctorK[==>, -->, A] =
    new ExofunctorK[==>, -->, A] { def map[F[_], G[_]](f: ∀[[a] =>> F[a] ==> G[a]]): A[F] --> A[G] = fn[F, G](f) }
