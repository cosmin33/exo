package io.cosmo.exo.categories.functors

import io.cosmo.exo.categories.{Endofunctor, Monoidal}

trait ExoSemigroupal[==>[_,_], -->[_,_], F[_]] extends Exofunctor[==>, -->, F] {
  type ⨂[_,_]
  type ⊙[_,_]
  def M1: Monoidal[==>, ⨂]
  def M2: Monoidal[-->, ⊙]

  def product[A, B](fn: F[A] ⨂ F[B]): F[A ⊙ B]

  def map2[A, B, C](fn: (A ⨂ B) ==> C): (F[A] ⨂ F[B]) --> F[C] = {

    val p: F[A] ⨂ F[B] => F[A ⊙ B] = product[A, B]

    val x: ((A ⨂ B) ==> C) => (F[A ⨂ B] --> F[C]) = map[A ⨂ B, C]



    ???
  }

}

trait ExoMonoidal[==>[_,_], -->[_,_], F[_]] extends ExoSemigroupal[==>, -->, F] {
  def point[A](a: A): F[A]
}