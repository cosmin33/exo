package io.cosmo.exo

type FunK2[A, B] = ArrowK2[Function, A, B]
object FunK2 {
  type Aux[A, B, F[_,_], G[_,_]] = FunK2[A, B] { type TypeA[a,b] = F[a,b]; type TypeB[a,b] = G[a,b] }
  def apply[F[_,_], G[_,_], A, B](f: F ~~> G)(using a: IsKind2.Aux[A, F], b: IsKind2.Aux[B, G]): FunK2[A, B] =
    new FunK2[A, B] { type TypeA[a,b] = F[a,b]; type TypeB[a,b] = G[a,b]; val (kindA, kindB, fn) = (a, b, f) }

  def isoFunK2Unapply[A, B](i: IsoFunK2[A, B])(using a: IsKind2[A], b: IsKind2[B]): a.Type <~~> b.Type =
    <~~>.unsafe(i.to.unapply, i.from.unapply)
}
