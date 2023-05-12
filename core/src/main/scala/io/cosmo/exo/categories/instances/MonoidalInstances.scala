package io.cosmo.exo.categories.instances

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.{Exo, Exobifunctor}
import io.cosmo.exo.evidence.NotEqK2
import io.cosmo.exo.typeclasses.TypeK

class MonoidalInstances {

  def exoMonoidalIdIsoFun[->[_, _], ⊙[_, _], TC0[_]](implicit
    B1: Exobifunctor.EndoPro[* => *, ->],
    B2: Exobifunctor.Endo[* => *, ⊙]
  ): Exo.IsoFun[* => *, Monoidal.Aux[->, ⊙, TC0, *]] =
    new Exo.IsoFun[* => *, Monoidal.Aux[->, ⊙, TC0, *]] {
      def map[A, B](iso: Iso[* => *, A, B]): Monoidal.Aux[->, ⊙, TC0, A] => Monoidal.Aux[->, ⊙, TC0, B] =
        ma => new Monoidal.ProtoFromAssociative[->, ⊙, TC0](ma) {
          type Id = B
          def idl  [X: TC]: ⊙[B, X] -> X = B1.leftMap(Dual(B2.leftMap[B, X, A](iso.from)))(SubcatHasId[* => *, X]).apply(ma.idl)
          def coidl[X: TC]: X -> ⊙[B, X] = B1.rightMap(Dual(B2.leftMap[A, X, B](iso.to)))(SubcatHasId[Dual[* => *,*,*], X]).apply(ma.coidl)
          def idr  [X: TC]: ⊙[X, B] -> X = B1.leftMap(Dual(B2.rightMap[X, B, A](iso.from)))(SubcatHasId[* => *, X]).apply(ma.idr)
          def coidr[X: TC]: X -> ⊙[X, B] = B1.rightMap(Dual(B2.rightMap[X, A, B](iso.to)))(SubcatHasId[Dual[* => *,*,*], X]).apply(ma.coidr)
        }
    }

  implicit def exoMonoidalIdIsoIsoImp[->[_, _], ⊙[_, _], TC0[_]](implicit
    B1: Exobifunctor.EndoPro[* => *, ->],
    B2: Exobifunctor.Endo[* => *, ⊙],
    neq: NotEqK2[->, * => *] // otherwise would collide at implicit search with exoMonoidalIdIso when -> is Function1
  ): Exo.IsoIso[* => *, Monoidal.Aux[->, ⊙, TC0, *]] = Exo.unsafeIsoFunToIsoIso(exoMonoidalIdIsoFun)

  implicit def exoMonoidalIdIso[->[_, _], ⊙[_, _], TC0[_]]: Exo.IsoFun[->, Monoidal.Aux[->, ⊙, TC0, *]] =
    new Exo[Iso[->,*,*], * => *, Monoidal.Aux[->, ⊙, TC0, *]] {
      def map[A, B](iso: Iso[->, A, B]): Monoidal.Aux[->, ⊙, TC0, A] => Monoidal.Aux[->, ⊙, TC0, B] =
        ma => new Monoidal.ProtoFromAssociative[->, ⊙, TC0](ma) {
          type Id = B
          implicit val currCategory: Subcat.Aux[->, TC0] = C
          def idl  [X: TC]: ⊙[B, X] -> X = C.andThen(ma.bifunctor.leftMap[B, X, A](iso.from), ma.idl)
          def coidl[X: TC]: X -> ⊙[B, X] = C.andThen(ma.coidl, ma.bifunctor.leftMap[A, X, B](iso.to))
          def idr  [X: TC]: ⊙[X, B] -> X = C.andThen(ma.bifunctor.rightMap[X, B, A](iso.from), ma.idr)
          def coidr[X: TC]: X -> ⊙[X, B] = C.andThen(ma.coidr, ma.bifunctor.rightMap[X, A, B](iso.to))
        }
    }

//  implicit def exoMonoidalTCIso[->[_, _], ⊙[_, _], I, TC0[_], TC1[_]](implicit
//    isoTc: IsoFunK[TypeK[TC0], TypeK[TC1]]
//  ): Exo[Iso[->,*,*], FunK, TypeK[Monoidal.Aux[->, ⊙, *[_], I]]] = ???
//    new Exo[IsoFunK, FunK, TypeK[Monoidal.Aux[->, ⊙, *[_], I]]] {
//      override def map[A, B](f: Iso[FunK, A, B]): FunK[TypeK[Monoidal.Aux[->, ⊙, *[_], I]][A], TypeK[Monoidal.Aux[->, ⊙, *[_], I]][B]] = ???
//    }

  type TypeH[H[_[_]], A] = H[IsKind[A]#Type]

  def monoidalTcMap[->[_,_], ⊙[_, _], I, F[_], G[_]](gtof: G ~> F): Monoidal.Aux[->, ⊙, F, I] => Monoidal.Aux[->, ⊙, G, I] =
    (m: Monoidal.Aux[->, ⊙, F, I]) => {
      new Monoidal[->, ⊙] {
        type TC[a] = G[a]
        type Id = I
        def C: Subcat.Aux[->, G] = ???
        def bifunctor: Endobifunctor[->, ⊙] = m.bifunctor
        def idl  [X: G]: ⊙[I, X] -> X = m.idl[X](gtof.apply[X](implicitly[G[X]]))
        def coidl[A: G]: A -> (I ⊙ A) = m.coidl[A](gtof.apply[A](implicitly[G[A]]))
        def idr  [A: G]: A ⊙ I -> A = m.idr[A](gtof.apply[A](implicitly[G[A]]))
        def coidr[A: G]: A -> (A ⊙ I) = m.coidr[A](gtof.apply[A](implicitly[G[A]]))
        def associate  [X: G, Y: G, Z: G]: X ⊙ Y ⊙ Z -> (X ⊙ (Y ⊙ Z)) =
          m.associate[X, Y, Z](gtof[X](implicitly[G[X]]), gtof[Y](implicitly[G[Y]]), gtof[Z](implicitly[G[Z]]))
        def diassociate[X: G, Y: G, Z: G]: X ⊙ (Y ⊙ Z) -> (X ⊙ Y ⊙ Z) =
          m.diassociate[X, Y, Z](gtof[X](implicitly[G[X]]), gtof[Y](implicitly[G[Y]]), gtof[Z](implicitly[G[Z]]))
      }
    }

  def monoidalTcMap1[->[_, _], ⊙[_, _], I, A, B](ba: FunK[B, A])
  : Monoidal.Aux[->, ⊙, ba.TypeB, I] => Monoidal.Aux[->, ⊙, ba.TypeA, I] =
      monoidalTcMap[->, ⊙, I, ba.TypeB, ba.TypeA](ba.fn)

}
