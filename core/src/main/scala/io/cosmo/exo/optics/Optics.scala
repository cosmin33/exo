package io.cosmo.exo.optics

import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.Exobifunctor

object Optics {

  trait Lens[S, T, A, B] {
    def view: S => A
    def update: (B, S) => T
  }

  trait Prism[S, T, A, B] {
    def partial: S => Either[A, T]
    def build: B => T
  }

  trait Affine[S, T, A, B] {
    def preview: S => Either[A, T]
    def set: (B, S) => T
  }

  trait Traversal[S, T, A, B] {
    def contents: S => List[A]
    def fill: (List[B], S) => T
  }

  trait LensP[S, T, A, B] extends Lens[S, T, A, B] {
    def run[P[_,_]](implicit
      P: Exobifunctor[Dual[* => *,*,*], * => *, * => *, P],
      C: Cartesian.Aux[P, Tuple2, Trivial.T1, Unit]
    ): P[A, B] => P[S, T] = {
      val xx: P[A, B] => P[S, B] = P.bimap(Dual(view), identity[B])
      //val r1: P[S, B] => P[S, (B, S)] = (psb: P[S, B]) => C.merge(psb, C.C.id[S])
      val mm = (psb: P[S, B]) => P.rightMap[S, (B, S), T](update.tupled)(implicitly)(C.merge(psb, C.C.id[S]))
      xx andThen mm

    }
  }

  trait LensX[->[_,_], ⨂[_,_], S, T, A, B] {
    def view: S -> A
    def update: ⨂[B, S] -> T
  }

  trait LensXP[->[_,_], ⨂[_,_], S, T, A, B] extends LensX[->, ⨂, S, T, A, B] {
    def run[P[_,_]](implicit
      P: Exobifunctor[Dual[->,*,*], ->, ->, P],
      C: Cartesian[P, ⨂]
    ): P[A, B] -> P[S, T] = {
      val v: S -> A = view
      val u: (B ⨂ S) -> T = update
      val x1: P[S, S ⨂ S] = C.diag[S](???)
      //val mm = C.merge()
      ???
    }
  }


}
