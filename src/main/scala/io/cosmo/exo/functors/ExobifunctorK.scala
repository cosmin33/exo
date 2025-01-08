package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._
import io.cosmo.exo.internal._

trait ExobifunctorK[==>[_,_], -->[_,_], >->[_,_], ⊙[_[_], _[_]]]:
  def bimap[F[_], X[_], G[_], Y[_]](l: ∀[[a] =>> F[a] ==> X[a]], r: ∀[[a] =>> G[a] --> Y[a]]): ⊙[F, G] >-> ⊙[X, Y]

  def leftMap[F[_], G[_], Z[_]](fn: ∀[[a] =>> F[a] ==> Z[a]])(using C: SubcatKHasId[-->, G]): ⊙[F, G] >-> ⊙[Z, G] = bimap(fn, C.id)
  def rightMap[F[_], G[_], Z[_]](fn: ∀[[a] =>> G[a] --> Z[a]])(using C: SubcatKHasId[==>, F]): ⊙[F, G] >-> ⊙[F, Z] = bimap(C.id, fn)

  def leftFunctor[X[_]](using C: SubcatKHasId[-->, X]): ExoK[==>, >->, [f[_]] =>> ⊙[f, X]] =
    ExoK.unsafe[==>, >->, [f[_]] =>> ⊙[f, X]]([f[_], g[_]] => (fn: ∀[[a] =>> f[a] ==> g[a]]) => leftMap(fn))
  def rightFunctor[X[_]](using C: SubcatKHasId[==>, X]): ExoK[-->, >->, [f[_]] =>> ⊙[X, f]] =
    ExoK.unsafe[-->, >->, [f[_]] =>> ⊙[X, f]]([f[_], g[_]] => (fn: ∀[[a] =>> f[a] --> g[a]]) => rightMap(fn))

object ExobifunctorK:
  def apply[==>[_,_], -->[_,_], >->[_,_], ⊙[_[_], _[_]]](using E: ExobifunctorK[==>, -->, >->, ⊙]): ExobifunctorK[==>, -->, >->, ⊙] = E
  type Con[==>[_,_], -->[_,_], >->[_,_], B[_[_], _[_]]] = ExobifunctorK[Dual[==>, *, *], Dual[-->, *, *], >->, B]
  type ConF[B[_[_], _[_]]] = Con[* => *, * => *, * => *, B]

