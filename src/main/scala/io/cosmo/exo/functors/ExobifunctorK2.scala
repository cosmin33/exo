package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._
import io.cosmo.exo.internal._

trait ExobifunctorK2[==>[_,_], -->[_,_], >->[_,_], ⊙[_[_,_], _[_,_]]]:
  def bimap[F[_,_], X[_,_], G[_,_], Y[_,_]](l: ∀∀[[a, b] =>> F[a, b] ==> X[a, b]], r: ∀∀[[a, b] =>> G[a, b] --> Y[a, b]]): ⊙[F, G] >-> ⊙[X, Y]

  def leftMap[F[_,_], G[_,_], Z[_,_]](fn: ∀∀[[a, b] =>> F[a, b] ==> Z[a, b]])(using C: SubcatK2HasId[-->, G]): ⊙[F, G] >-> ⊙[Z, G] = bimap(fn, C.id)
  def rightMap[F[_,_], G[_,_], Z[_,_]](fn: ∀∀[[a, b] =>> G[a, b] --> Z[a, b]])(using C: SubcatK2HasId[==>, F]): ⊙[F, G] >-> ⊙[F, Z] = bimap(C.id, fn)

  def leftFunctor[X[_,_]](using C: SubcatK2HasId[-->, X]): ExoK2[==>, >->, [f[_,_]] =>> ⊙[f, X]] =
    ExoK2.unsafe[==>, >->, [f[_,_]] =>> ⊙[f, X]]([f[_,_], g[_,_]] => (fn: ∀∀[[a, b] =>> f[a, b] ==> g[a, b]]) => leftMap(fn))
  def rightFunctor[X[_,_]](using C: SubcatK2HasId[==>, X]): ExoK2[-->, >->, [f[_,_]] =>> ⊙[X, f]] =
    ExoK2.unsafe[-->, >->, [f[_,_]] =>> ⊙[X, f]]([f[_,_], g[_,_]] => (fn: ∀∀[[a, b] =>> f[a, b] --> g[a, b]]) => rightMap(fn))

object ExobifunctorK2:
  def apply[==>[_,_], -->[_,_], >->[_,_], ⊙[_[_,_], _[_,_]]](using E: ExobifunctorK2[==>, -->, >->, ⊙]): ExobifunctorK2[==>, -->, >->, ⊙] = E
  type Con[==>[_,_], -->[_,_], >->[_,_], B[_[_], _[_]]] = ExobifunctorK[Dual[==>,*,*], Dual[-->,*,*], >->, B]
  type ConF[B[_[_], _[_]]] = Con[* => *, * => *, * => *, B]
