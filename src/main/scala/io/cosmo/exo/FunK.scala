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

object FunK extends FunkImplicits {
  type Aux[A, B, F[_], G[_]] = FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a] }
  def apply[F[_], G[_], A, B](f: F ~> G)(using a: IsKind.Aux[A, F], b: IsKind.Aux[B, G]): FunK[A, B] =
    new FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a]; val (kindA, kindB, fn) = (a, b, f) }

  def isoFunKUnapply[A, B, F[_], G[_]](i: IsoFunK[A, B])(using a: IsKind.Aux[A, F], b: IsKind.Aux[B, G]): F <~> G =
    <~>.unsafe(i.to.unapply, i.from.unapply)

  given isoFunkCanonic   [A, B](using a: IsKind[A], b: IsKind[B]): (FunK[A, B] <=> (a.Type ~> b.Type)) = Iso.unsafe(_.unapply, apply)
  given isoIsoFunkCanonic[A, B](using a: IsKind[A], b: IsKind[B]): (IsoFunK[A, B] <=> (a.Type <~> b.Type)) =
    Iso.unsafe(i => <~>.unsafe(i.to.unapply, i.from.unapply), i => Iso.unsafe(apply(i.to), apply(i.from)))

}

import FunKHelpers.*

trait FunkImplicits extends FunkImplicits01 {
  given bifunctorTuple: Endobifunctor[FunK, Tuple2] = new FunkBifTuple {}
  given bifunctorEither: Endobifunctor[FunK, Either] = new FunkBifEither {}

  given distributeTupleEither: Distributive.Aux[FunK, IsKind, Tuple2, TypeK[UnitK], Either, TypeK[VoidK]] = new FunkSubcat {}

  given initial: Initial.Aux[FunK, IsKind, TypeK[VoidK]] = new FunkInitial {}
  given terminal: Terminal.Aux[FunK, IsKind, TypeK[UnitK]] = new FunKTerminal {}

  given cccTuple: Ccc.Aux[FunK, Tuple2, IsKind, TypeK[UnitK], FunK] = new FunkCccTuple {}
  given cccConjunction: Ccc.Aux[FunK, /\, IsKind, TypeK[UnitK], FunK] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> Ccc.Aux[FunK, f, IsKind, TypeK[UnitK], FunK]](cccTuple)
  given cocartesianOppEither: Cartesian.Aux[Opp[FunK]#l, Either, IsKind, TypeK[VoidK]] = new FunkCocartesianEither {}
  given cocartesianEither: Cartesian.Aux[Dual[FunK,*,*], Either, IsKind, TypeK[VoidK]] =
    Dual.leibniz[FunK].subst[[f[_,_]] =>> Cartesian.Aux[f[_,_], Either, IsKind, TypeK[VoidK]]](cocartesianOppEither)
  given cocartesianDisjunction: Cocartesian.Aux[FunK, \/, IsKind, TypeK[VoidK]] =
    \/.unsafeLeibniz.subst[[f[_,_]] =>> Cocartesian.Aux[FunK, f, IsKind, TypeK[VoidK]]](cocartesianEither)
}

trait FunkImplicits01 {
  given distributeConjDisj: Distributive.Aux[FunK, IsKind, /\, TypeK[UnitK], \/, TypeK[VoidK]] =
    =~~=.lower2[[f[_,_], g[_,_]] =>> Distributive.Aux[FunK, IsKind, f, TypeK[UnitK], g, TypeK[VoidK]]]
      .on(/\.unsafeLeibniz, \/.unsafeLeibniz)(FunK.distributeTupleEither)
}

object FunKHelpers {

  trait FunkBifTuple extends Endobifunctor[FunK, Tuple2]:
    def bimap[A, X, B, Y](left: FunK[A, X], right: FunK[B, Y]): FunK[(A, B), (X, Y)] =
      FunK(~>.product.bimap(left.fn, right.fn))(using
        IsKind.pair2(using left.kindA, right.kindA),
        IsKind.pair2(using left.kindB, right.kindB)
      )

  trait FunkBifEither extends Endobifunctor[FunK, Either]:
    def bimap[A, X, B, Y](l: FunK[A, X], r: FunK[B, Y]): FunK[Either[A, B], Either[X, Y]] =
      FunK(~>.coproduct.bimap(l.fn, r.fn))(using IsKind.either2(using l.kindA, r.kindA), IsKind.either2(using l.kindB, r.kindB))

  trait FunkSubcat extends Distributive.Proto[FunK, IsKind, Tuple2, TypeK[UnitK], Either, TypeK[VoidK]] {
    def id[A](using A: IsKind[A]): FunK[A, A] = FunK(~>.id[A.Type])
    def andThen[A, B, C](ab: FunK[A, B], bc: FunK[B, C]): FunK[A, C] =
      FunK(~>.andThen(ab.fn, IsKind.injectivity(bc.kindA, ab.kindB).subst[[f[_]] =>> f ~> bc.TypeB](bc.fn)))(using ab.kindA, bc.kindB)
    def cartesian:   Cartesian.Aux[FunK, Tuple2, IsKind, TypeK[UnitK]] = summon
    def cocartesian: Cocartesian.Aux[FunK, Either, IsKind, TypeK[VoidK]] = summon
    def distribute[A, B, C](using ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): FunK[(A, Either[B, C]), Either[(A, B), (A, C)]] =
      FunK(~>.distribute[ia.Type, ib.Type, ic.Type])(using IsKind.pair2[A, Either[B, C]], IsKind.either2[(A, B), (A, C)])
  }

  trait FunkInitial extends Initial.Proto[FunK, IsKind, TypeK[VoidK]] {
    def subcat: Subcategory.Aux[FunK, IsKind] = summon
    def TC: IsKind[TypeK[VoidK]] = summon
    def initiate[A](using A: IsKind[A]): FunK[TypeK[VoidK], A] = FunK(~>.initiate[A.Type])
  }

  class FunKTerminal extends Terminal.Proto[FunK, IsKind, TypeK[UnitK]] {
    def TC: IsKind[TypeK[UnitK]] = summon
    def subcat: Subcategory.Aux[Dual[FunK,_,_], IsKind] = Semicategory.dualSubcat[FunK, IsKind]
    def terminate[A](using A: IsKind[A]): FunK[A, TypeK[UnitK]] = FunK(~>.terminate[A.Type])
  }

  trait FunkCccTuple extends Ccc.Proto[FunK, Tuple2, IsKind, TypeK[UnitK], FunK] {
    def C: Subcat.Aux[FunK, IsKind] = summon
    def bifunctor: Endobifunctor[FunK, Tuple2] = summon
    def associate  [X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[((X, Y), Z), (X, (Y, Z))] =
      FunK(~>.product.associate[ix.Type, iy.Type, iz.Type])(using
        IsKind.pair2[(X, Y), Z],
        IsKind.pair2[X, (Y, Z)]
      )
    def diassociate[X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[(X, (Y, Z)), ((X, Y), Z)] =
      FunK(~>.product.diassociate[ix.Type, iy.Type, iz.Type])(using
        IsKind.pair2[X, (Y, Z)],
        IsKind.pair2[(X, Y), Z]
      )
    def fst[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), A] =
      FunK(~>.product.fst[ia.Type, ib.Type])(using IsKind.pair2[A, B], ia)
    def snd[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), B] =
      FunK(~>.product.snd[ia.Type, ib.Type])(using IsKind.pair2[A, B], ib)
    def diag[A](using ia: IsKind[A]): FunK[A, (A, A)] =
      FunK(~>.product.diag[ia.Type])(using ia, IsKind.pair2(using ia, ia))
    def &&&[X, Y, Z](f: FunK[X, Y], g: FunK[X, Z]): FunK[X, (Y, Z)] =
      FunK(
        ~>.product.merge(f.fn, IsKind.injectivity(g.kindA, f.kindA).subst[[f[_]] =>> f ~> g.TypeB](g.fn))
      )(using f.kindA, IsKind.pair2(using f.kindB, g.kindB))
    def idl  [A](using ia: IsKind[A]): FunK[(TypeK[UnitK], A), A] =
      FunK(~>.product.idl[ia.Type])(using IsKind.pair2[TypeK[UnitK], A], ia)
    def coidl[A](using ia: IsKind[A]): FunK[A, (TypeK[UnitK], A)] =
      FunK(~>.product.coidl[ia.Type])(using ia, IsKind.pair2[TypeK[UnitK], A])
    def idr  [A](using ia: IsKind[A]): FunK[(A, TypeK[UnitK]), A] =
      FunK(~>.product.idr[ia.Type])(using IsKind.pair2[A, TypeK[UnitK]], ia)
    def coidr[A](using ia: IsKind[A]): FunK[A, (A, TypeK[UnitK])] =
      FunK(~>.product.coidr[ia.Type])(using ia, IsKind.pair2[A, TypeK[UnitK]])
    def braid[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), (B, A)] =
      FunK(~>.product.braid[ia.Type, ib.Type])(using IsKind.pair2[A, B], IsKind.pair2[B, A])
    def curry[A, B, C](f: FunK[(A, B), C]): FunK[A, FunK[B, C]] = {
      given c: IsKind.Aux[C, f.TypeB] = f.kindB
      val (ia, ib) = f.kindA.tuple[A, B]
      val fun = IsKind.injectivity(f.kindA, IsKind.pair2[A, B](using ia, ib)).subst[[f[_]] =>> f ~> f.TypeB](f.fn)
      FunK[ia.Type, [o] =>> ib.Type[o] => c.Type[o], A, FunK[B, C]](~>.product.curry(fun))(using ia, IsKind.function[B, C](using ib, c))
    }
    def uncurry[A, B, C](f: FunK[A, FunK[B, C]]): FunK[(A, B), C] = {
      given a: IsKind.Aux[A, f.TypeA] = f.kindA
      val (ib, ic) = f.kindB.funk[B, C]
      val fun = IsKind.injectivity(f.kindB, IsKind.function[B, C](using ib, ic)).subst[[f[_]] =>> f.TypeA ~> f](f.fn)
      FunK[[o] =>> (a.Type[o], ib.Type[o]), ic.Type, (A, B), C](~>.product.uncurry(fun))(using IsKind.pair2[A, B](using a, ib), ic)
    }
  }

  trait FunkCocartesianEither extends Cartesian.Proto[Opp[FunK]#l, Either, IsKind, TypeK[VoidK]] {
    def bifunctor = Exobifunctor.oppEndobifunctor[FunK, Either]
    def C = Semicategory.oppSubcat[FunK, IsKind]
    def associate  [X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[X, Either[Y, Z]], Either[Either[X, Y], Z]] =
      FunK(~>.coproduct.associate[ix.Type, iy.Type, iz.Type])(using
        IsKind.either2[X, Either[Y, Z]],
        IsKind.either2[Either[X, Y], Z]
      )
    def diassociate[X, Y, Z](using ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[Either[X, Y], Z], Either[X, Either[Y, Z]]] =
      FunK(~>.coproduct.diassociate[ix.Type, iy.Type, iz.Type])(using
        IsKind.either2[Either[X, Y], Z],
        IsKind.either2[X, Either[Y, Z]]
      )
    def fst[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[A, Either[A, B]] =
      FunK(~>.coproduct.inl[ia.Type, ib.Type])(using ia, IsKind.either2[A, B])
    def snd[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[B, Either[A, B]] =
      FunK(~>.coproduct.inr[ia.Type, ib.Type])(using ib, IsKind.either2[A, B])
    def diag[A](using ia: IsKind[A]): FunK[Either[A, A], A] =
      FunK(~>.coproduct.codiag[ia.Type])(using IsKind.either2[A, A], ia)
    def &&&[X, Y, Z](f: FunK[Y, X], g: FunK[Z, X]): FunK[Either[Y, Z], X] =
      FunK(~>.coproduct.split(f.fn, IsKind.injectivity(g.kindB, f.kindB).subst[[f[_]] =>> g.TypeA ~> f](g.fn))
      )(using IsKind.either2(using f.kindA, g.kindA), f.kindB)
    def idl  [A](using ia: IsKind[A]): FunK[A, Either[TypeK[VoidK], A]] =
      FunK(~>.coproduct.idl[ia.Type])(using ia, IsKind.either2[TypeK[VoidK], A])
    def coidl[A](using ia: IsKind[A]): FunK[Either[TypeK[VoidK], A], A] =
      FunK(~>.coproduct.coidl[ia.Type])(using IsKind.either2[TypeK[VoidK], A], ia)
    def idr  [A](using ia: IsKind[A]): FunK[A, Either[A, TypeK[VoidK]]] =
      FunK(~>.coproduct.idr[ia.Type])(using ia, IsKind.either2[A, TypeK[VoidK]])
    def coidr[A](using ia: IsKind[A]): FunK[Either[A, TypeK[VoidK]], A] =
      FunK(~>.coproduct.coidr[ia.Type])(using IsKind.either2[A, TypeK[VoidK]], ia)
    def braid[A, B](using ia: IsKind[A], ib: IsKind[B]): FunK[Either[B, A], Either[A, B]] =
      FunK(~>.coproduct.braid[ib.Type, ia.Type])(using IsKind.either2[B, A], IsKind.either2[A, B])
  }

}
