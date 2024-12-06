package io.cosmo.exo

type FunH[A, B] = ArrowH[Function, A, B]
object FunH {
  type Aux[A, B, F[_[_]], G[_[_]]] = FunH[A, B] { type TypeA[f[_]] = F[f]; type TypeB[f[_]] = G[f] }
  def apply[F[_[_]], G[_[_]], A, B](f: F ≈> G)(using a: IsHKind.Aux[A, F], b: IsHKind.Aux[B, G]): FunH[A, B] =
    new FunH[A, B] { type TypeA[f[_]] = F[f]; type TypeB[f[_]] = G[f]; val (kindA, kindB, fn) = (a, b, f) }

  def isoFunHUnapply[A, B](i: IsoFunH[A, B])(using a: IsHKind[A], b: IsHKind[B]): a.Type <≈> b.Type =
    <≈>.unsafe(i.to.unapply, i.from.unapply)
}
