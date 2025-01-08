package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._
import io.cosmo.exo.internal._

trait ExobifunctorH[==>[_,_], -->[_,_], >->[_,_], ⊙[_[_[_]], _[_[_]]]]:
  def bimap[F[_[_]], X[_[_]], G[_[_]], Y[_[_]]](l: ∀~[[a[_]] =>> F[a] ==> X[a]], r: ∀~[[a[_]] =>> G[a] --> Y[a]]): ⊙[F, G] >-> ⊙[X, Y]

  def leftMap[F[_[_]], G[_[_]], Z[_[_]]](fn: ∀~[[a[_]] =>> F[a] ==> Z[a]])(using C: SubcatHHasId[-->, G]): ⊙[F, G] >-> ⊙[Z, G] = bimap(fn, C.id)
  def rightMap[F[_[_]], G[_[_]], Z[_[_]]](fn: ∀~[[a[_]] =>> G[a] --> Z[a]])(using C: SubcatHHasId[==>, F]): ⊙[F, G] >-> ⊙[F, Z] = bimap(C.id, fn)

  def leftFunctor[X[_[_]]](using C: SubcatHHasId[-->, X]): ExoH[==>, >->, [f[_[_]]] =>> ⊙[f, X]] =
    ExoH.unsafe[==>, >->, [f[_[_]]] =>> ⊙[f, X]]([f[_[_]], g[_[_]]] => (fn: ∀~[[a[_]] =>> f[a] ==> g[a]]) => leftMap(fn))
  def rightFunctor[X[_[_]]](using C: SubcatHHasId[==>, X]): ExoH[-->, >->, [f[_[_]]] =>> ⊙[X, f]] =
    ExoH.unsafe[-->, >->, [f[_[_]]] =>> ⊙[X, f]]([f[_[_]], g[_[_]]] => (fn: ∀~[[a[_]] =>> f[a] --> g[a]]) => rightMap(fn))

object ExobifunctorH:
  def apply[==>[_,_], -->[_,_], >->[_,_], ⊙[_[_[_]], _[_[_]]]](using E: ExobifunctorH[==>, -->, >->, ⊙]): ExobifunctorH[==>, -->, >->, ⊙] = E
  type Con[==>[_,_], -->[_,_], >->[_,_], B[_[_], _[_]]] = ExobifunctorK[Dual[==>,*,*], Dual[-->,*,*], >->, B]
  type ConF[B[_[_], _[_]]] = Con[* => *, * => *, * => *, B]
