package io.cosmo.exo.evidence

import io.cosmo.exo.typeclasses.{IsTypeF, TypeF}
import io.cosmo.exo.~>

trait IsInjectiveK[A[_[_]]] {

  def apply[F[_], G[_]](implicit ev: A[F] === A[G]): F =~= G

}


object Magarie1 {


//  trait Funktion[TF, TG] {
//    type F[_]
//    type G[_]
//    def eqA: TF === TypeF[F]
//    def eqB: TG === TypeF[G]
//    def instance: F ~> G
//  }

  type Funktion[A, B] = IsTypeF[A]#Type ~> IsTypeF[B]#Type



}