package io.cosmo.exo

type FunK[A, B] = ArrowK[Function, A, B]
object FunK {
  type Aux[A, B, F[_], G[_]] = FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a] }
  def apply[F[_], G[_], A, B](f: F ~> G)(using a: IsKind.Aux[A, F], b: IsKind.Aux[B, G]): FunK.Aux[A, B, F, G] =
    new FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a]; val (kindA, kindB, fn) = (a, b, f) }

  def isoFunKUnapply[A, B](i: IsoFunK[A, B])(using a: IsKind[A], b: IsKind[B]): a.Type <~> b.Type =
    <~>.unsafe(i.to.unapply, i.from.unapply)
}
