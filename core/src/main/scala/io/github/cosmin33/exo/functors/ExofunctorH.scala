package io.github.cosmin33.exo.functors

import io.github.cosmin33.exo.*
import io.github.cosmin33.exo.categories.*
import io.github.cosmin33.exo.evidence.*
import io.github.cosmin33.exo.syntax.*

trait ExofunctorH[==>[_,_], -->[_,_], A[_[_[_]]]]:
  def map[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] ==> G[a]]): A[F] --> A[G]
object ExofunctorH:
  def apply[==>[_,_], -->[_,_], A[_[_[_]]]](using E: ExofunctorH[==>, -->, A]): ExofunctorH[==>, -->, A] = E
  def unsafe[==>[_,_], -->[_,_], A[_[_[_]]]](fn: [F[_[_]], G[_[_]]] => ∀~[[a[_]] =>> F[a] ==> G[a]] => (A[F] --> A[G])): ExofunctorH[==>, -->, A] =
    new ExofunctorH[==>, -->, A] { def map[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] ==> G[a]]): A[F] --> A[G] = fn[F, G](f) }
