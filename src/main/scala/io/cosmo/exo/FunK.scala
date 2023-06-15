package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax.*

trait FunK[A, B]:
  type TypeA[_]
  type TypeB[_]
  def kindA: IsKind.Aux[A, TypeA]
  def kindB: IsKind.Aux[B, TypeB]
  def fn: TypeA ~> TypeB
  def unapply(using ia: IsKind[A], ib: IsKind[B]): ia.Type ~> ib.Type =
    IsK.lower2(IsKind.injectivity(kindA, ia), IsKind.injectivity(kindB, ib))(fn)

object FunK {
  type Aux[A, B, F[_], G[_]] = FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a] }
  def apply[F[_], G[_]](f: F ~> G): FunK.Aux[TypeK[F], TypeK[G], F, G] = FunK.from(f)(IsKind[TypeK[F]], IsKind[TypeK[G]])
  def from[F[_], G[_], A, B](f: F ~> G)(a: IsKind.Aux[A, F], b: IsKind.Aux[B, G]): FunK.Aux[A, B, F, G] =
    new FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a]; val (kindA, kindB, fn) = (a, b, f) }

  def isoFunKUnapply[A, B, F[_], G[_]](i: IsoFunK[A, B])(using a: IsKind.Aux[A, F], b: IsKind.Aux[B, G]): F <~> G =
    <~>.unsafe(i.to.unapply, i.from.unapply)

  given impIsoFunK[F[_], G[_]](using i: F <~> G): Iso[FunK, TypeK[F], TypeK[G]] = i.isoTo[Iso[FunK, TypeK[F], TypeK[G]]]

  given isoToFun[F[_], G[_]]: (FunK[TypeK[F], TypeK[G]] <=> (F ~> G)) = Iso.unsafe(_.unapply, apply)
  given isoKIso[F[_], G[_]]: (IsoFunK[TypeK[F], TypeK[G]] <=> (F <~> G)) =
    Iso.unsafe(i => <~>.unsafe(i.to.unapply, i.from.unapply), i => Iso.unsafe(apply(i.to), apply(i.from)))

  import FunKHelpers.*

  given subcat: Distributive.Aux[FunK, IsKind, (*, *), TypeK[UnitK], Either, TypeK[VoidK]] = ???
  given initial: Initial.Aux[FunK, IsKind, TypeK[VoidK]] = ???
  given terminal: Terminal.Aux[FunK, IsKind, TypeK[UnitK]] = ???

  given bifunctorTuple: Endobifunctor[FunK, Tuple2] = ???

  given bifunctorEither: Endobifunctor[FunK, Either] = ???

  given ccc: Ccc.Aux[FunK, Tuple2, IsKind, TypeK[UnitK], FunK] = ???
  given cocartesian: Cartesian.Aux[Dual[FunK,*,*], Either, IsKind, TypeK[VoidK]] = ???

  def cocartesianOpp: Cartesian.Aux[Opp[FunK]#l, Either, IsKind, TypeK[VoidK]] = ???
}

object FunKHelpers {

  trait FunkBifTuple extends Endobifunctor[FunK, Tuple2]:
    def bimap[A, X, B, Y](left: FunK[A, X], right: FunK[B, Y]): FunK[(A, B), (X, Y)] =
      FunK.from(
        ~>.product.bimap(left.fn, right.fn))(
        IsKind.pair2(using left.kindA, right.kindA),
        IsKind.pair2(using left.kindB, right.kindB)
      )

  trait FunkBifEither extends Endobifunctor[FunK, Either]:
    def bimap[A, X, B, Y](l: FunK[A, X], r: FunK[B, Y]): FunK[Either[A, B], Either[X, Y]] =
      FunK.from(~>.coproduct.bimap(l.fn, r.fn))(IsKind.either2(using l.kindA, r.kindA), IsKind.either2(using l.kindB, r.kindB))

  trait FunkCartesianTuple extends Ccc[FunK, Tuple2] {
    type Id = TypeK[UnitK]
    type TC[a] = IsKind[a]
    type |->[a, b] = FunK[a, b]
    def C: Subcat.Aux[FunK, IsKind] = summon
    def bifunctor: Endobifunctor[FunK, Tuple2] = summon
    def associate  [X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[((X, Y), Z), (X, (Y, Z))] =
      FunK.from(
        ~>.product.associate[ix.Type, iy.Type, iz.Type])(
        IsKind.pair2[(X, Y), Z],
        IsKind.pair2[X, (Y, Z)]
      )
    def diassociate[X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[(X, (Y, Z)), ((X, Y), Z)] =
      FunK.from(
        ~>.product.diassociate[ix.Type, iy.Type, iz.Type])(
        IsKind.pair2[X, (Y, Z)],
        IsKind.pair2[(X, Y), Z]
      )
    def fst[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), A] =
      FunK.from(~>.product.fst[ia.Type, ib.Type])(IsKind.pair2[A, B], ia)
    def snd[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), B] =
      FunK.from(~>.product.snd[ia.Type, ib.Type])(IsKind.pair2[A, B], ib)
    def diag[A](using ia: IsKind[A]): FunK[A, (A, A)] =
      FunK.from(~>.product.diag[ia.Type])(ia, IsKind.pair2(using ia, ia))
    def &&&[X, Y, Z](f: FunK[X, Y], g: FunK[X, Z]): FunK[X, (Y, Z)] =
      FunK.from(
        ~>.product.merge(f.fn, IsKind.injectivity(g.kindA, f.kindA).subst[[f[_]] =>> f ~> g.TypeB](g.fn))
      )(f.kindA, IsKind.pair2(using f.kindB, g.kindB))
    def idl  [A](using ia: IsKind[A]): FunK[(TypeK[UnitK], A), A] =
      FunK.from(~>.product.idl[ia.Type])(IsKind.pair2[TypeK[UnitK], A], ia)
    def coidl[A](using ia: IsKind[A]): FunK[A, (TypeK[UnitK], A)] =
      FunK.from(~>.product.coidl[ia.Type])(ia, IsKind.pair2[TypeK[UnitK], A])
    def idr  [A](using ia: IsKind[A]): FunK[(A, TypeK[UnitK]), A] =
      FunK.from(~>.product.idr[ia.Type])(IsKind.pair2[A, TypeK[UnitK]], ia)
    def coidr[A](using ia: IsKind[A]): FunK[A, (A, TypeK[UnitK])] =
      FunK.from(~>.product.coidr[ia.Type])(ia, IsKind.pair2[A, TypeK[UnitK]])
    def braid[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), (B, A)] =
      FunK.from(~>.product.braid[ia.Type, ib.Type])(IsKind.pair2[A, B], IsKind.pair2[B, A])
    def curry[A, B, C](f: FunK[(A, B), C]): FunK[A, FunK[B, C]] = {
      given c: IsKind.Aux[C, f.TypeB] = f.kindB
      val (ia, ib) = f.kindA.tuple[A, B]
      val fun = IsKind.injectivity(f.kindA, IsKind.pair2[A, B](using ia, ib)).subst[[f[_]] =>> f ~> f.TypeB](f.fn)
      FunK.from[ia.Type, [o] =>> ib.Type[o] => c.Type[o], A, FunK[B, C]](~>.product.curry(fun))(ia, IsKind.function[B, C](using ib, c))
    }
    def uncurry[A, B, C](f: FunK[A, FunK[B, C]]): FunK[(A, B), C] = {
      given a: IsKind.Aux[A, f.TypeA] = f.kindA
      val (ib, ic) = f.kindB.funk[B, C]
      val fun = IsKind.injectivity(f.kindB, IsKind.function[B, C](using ib, ic)).subst[[f[_]] =>> f.TypeA ~> f](f.fn)
      FunK.from[[o] =>> (a.Type[o], ib.Type[o]), ic.Type, (A, B), C](~>.product.uncurry(fun))(IsKind.pair2[A, B](using a, ib), ic)
    }
  }

  trait FunkCocartesianEither extends Cartesian[Opp[FunK]#l, Either] {
    type Id = TypeK[VoidK]
    type TC[a] = IsKind[a]
    def bifunctor = Exobifunctor.oppEndobifunctor[FunK, Either]
    def C = Semicategory.oppSubcat[FunK, IsKind]
    def associate  [X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[X, Either[Y, Z]], Either[Either[X, Y], Z]] =
      FunK.from(
        ~>.coproduct.associate[ix.Type, iy.Type, iz.Type])(
        IsKind.either2(using ix, IsKind.either2(using iy, iz)),
        IsKind.either2(using IsKind.either2(using ix, iy), iz)
      )
    def diassociate[X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[Either[X, Y], Z], Either[X, Either[Y, Z]]] =
      FunK.from(
        ~>.coproduct.diassociate[ix.Type, iy.Type, iz.Type])(
        IsKind.either2(using IsKind.either2(using ix, iy), iz),
        IsKind.either2(using ix, IsKind.either2(using iy, iz))
      )
    def fst[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[A, Either[A, B]] =
      FunK.from(~>.coproduct.inl[ia.Type, ib.Type])(ia, IsKind.either2(using ia, ib))
    def snd[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[B, Either[A, B]] =
      FunK.from(~>.coproduct.inr[ia.Type, ib.Type])(ib, IsKind.either2(using ia, ib))
    def diag[A](using ia: IsKind[A]): FunK[Either[A, A], A] =
      FunK.from(~>.coproduct.codiag[ia.Type])(IsKind.either2(using ia, ia), ia)
    def &&&[X, Y, Z](f: FunK[Y, X], g: FunK[Z, X]): FunK[Either[Y, Z], X] =
      FunK.from(
        ~>.coproduct.split(f.fn, IsKind.injectivity(g.kindB, f.kindB).subst[[f[_]] =>> g.TypeA ~> f](g.fn))
      )(IsKind.either2(using f.kindA, g.kindA), f.kindB)
    def idl  [A](using ia: IsKind[A]): FunK[A, Either[TypeK[VoidK], A]] =
      FunK.from(~>.coproduct.idl[ia.Type])(ia, IsKind.either2(using IsKind[TypeK[VoidK]], ia))
    def coidl[A](using ia: IsKind[A]): FunK[Either[TypeK[VoidK], A], A] =
      FunK.from(~>.coproduct.coidl[ia.Type])(IsKind.either2(using IsKind[TypeK[VoidK]], ia), ia)
    def idr  [A](using ia: IsKind[A]): FunK[A, Either[A, TypeK[VoidK]]] =
      FunK.from(~>.coproduct.idr[ia.Type])(ia, IsKind.either2(using ia, IsKind[TypeK[VoidK]]))
    def coidr[A](using ia: IsKind[A]): FunK[Either[A, TypeK[VoidK]], A] =
      FunK.from(~>.coproduct.coidr[ia.Type])(IsKind.either2(using ia, IsKind[TypeK[VoidK]]), ia)
    def braid[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[Either[B, A], Either[A, B]] =
      FunK.from(~>.coproduct.braid[ib.Type, ia.Type])(IsKind.either2(using ib, ia), IsKind.either2(using ia, ib))
  }

}
