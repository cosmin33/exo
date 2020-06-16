package io.cosmo.exo.categories.instances

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.{Exo, Exobifunctor}
import io.cosmo.exo.evidence.NotEqK2

class MonoidalInstances {

  def exoMonoidalIdIsoFun[->[_, _], ⊙[_, _], TC0[_]](implicit
    B1: Exobifunctor.EndoPro[* => *, ->],
    B2: Exobifunctor.Endo[* => *, ⊙]
  ): Exo.IsoFun[* => *, Monoidal.Aux[->, ⊙, TC0, *]] =
    new Exo.IsoFun[* => *, Monoidal.Aux[->, ⊙, TC0, *]] {
      def map[A, B](iso: Iso[* => *, A, B]): Monoidal.Aux[->, ⊙, TC0, A] => Monoidal.Aux[->, ⊙, TC0, B] =
        ma => new Monoidal.ProtoFromAssociative[->, ⊙, TC0](ma) {
          type Id = B
          def idl  [X]: ⊙[B, X] -> X = B1.leftMap(Dual(B2.leftMap[B, X, A](iso.from)))(ma.idl)
          def coidl[X]: X -> ⊙[B, X] = B1.rightMap(Dual(B2.leftMap[A, X, B](iso.to)))(ma.coidl)
          def idr  [X]: ⊙[X, B] -> X = B1.leftMap(Dual(B2.rightMap[X, B, A](iso.from)))(ma.idr)
          def coidr[X]: X -> ⊙[X, B] = B1.rightMap(Dual(B2.rightMap[X, A, B](iso.to)))(ma.coidr)
        }
    }

  implicit def exoMonoidalIdIsoFunImp[->[_, _], ⊙[_, _], TC0[_]](implicit
    B1: Exobifunctor.EndoPro[* => *, ->],
    B2: Exobifunctor.Endo[* => *, ⊙],
    neq: NotEqK2[->, * => *] // otherwise would collide at implicit search with exoMonoidalIdIso when -> is Function1
  ): Exo.IsoFun[* => *, Monoidal.Aux[->, ⊙, TC0, *]] = exoMonoidalIdIsoFun

  implicit def exoMonoidalIdIso[->[_, _], ⊙[_, _], TC0[_]]: Exo.IsoFun[->, Monoidal.Aux[->, ⊙, TC0, *]] =
    new Exo[Iso[->,*,*], * => *, Monoidal.Aux[->, ⊙, TC0, *]] {
      def map[A, B](iso: Iso[->, A, B]): Monoidal.Aux[->, ⊙, TC0, A] => Monoidal.Aux[->, ⊙, TC0, B] =
        ma => new Monoidal.ProtoFromAssociative[->, ⊙, TC0](ma) {
          type Id = B
          def idl  [X]: ⊙[B, X] -> X = C.andThen(ma.bifunctor.leftMap[B, X, A](iso.from), ma.idl)
          def coidl[X]: X -> ⊙[B, X] = C.andThen(ma.coidl, ma.bifunctor.leftMap[A, X, B](iso.to))
          def idr  [X]: ⊙[X, B] -> X = C.andThen(ma.bifunctor.rightMap[X, B, A](iso.from), ma.idr)
          def coidr[X]: X -> ⊙[X, B] = C.andThen(ma.coidr, ma.bifunctor.rightMap[X, A, B](iso.to))
        }
    }

}
