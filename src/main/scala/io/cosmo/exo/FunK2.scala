package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax.*

trait FunK2[A, B] {
  type TypeA[_,_]
  type TypeB[_,_]

  def kindA: IsKind2.Aux[A, TypeA]
  def kindB: IsKind2.Aux[B, TypeB]

  def fn: TypeA ~~> TypeB
  def unapply(using ia: IsKind2[A], ib: IsKind2[B]): ia.Type ~~> ib.Type =
    IsK2.lower2.on(IsKind2.injectivity(kindA, ia), IsKind2.injectivity(kindB, ib))(fn)

}

object FunK2 extends Funk2Implicits {
  type Aux[A, B, F[_,_], G[_,_]] = FunK2[A, B] { type TypeA[a,b] = F[a,b]; type TypeB[a,b] = G[a,b] }
  def apply[F[_,_], G[_,_], A, B](f: F ~~> G)(using a: IsKind2.Aux[A, F], b: IsKind2.Aux[B, G]): FunK2[A, B] =
    new FunK2[A, B] { type TypeA[a,b] = F[a,b]; type TypeB[a,b] = G[a,b]; val (kindA, kindB, fn) = (a, b, f) }

  def isoFunK2Unapply[A, B](i: IsoFunK2[A, B])(using a: IsKind2[A], b: IsKind2[B]): a.Type <~~> b.Type =
    <~~>.unsafe(i.to.unapply, i.from.unapply)
}

import FunK2Helpers.*

trait Funk2Implicits extends FunkImplicits01 {
  given bifunctorTuple: Endobifunctor[FunK2, Tuple2] = new Funk2BifTuple {}
  given bifunctorEither: Endobifunctor[FunK2, Either] = new Funk2BifEither {}

  given distributeTupleEither: Distributive.Aux[FunK2, IsKind2, Tuple2, TypeK2[UnitK2], Either, TypeK2[VoidK2]] = new Funk2Subcat {}

  given initial: Initial.Aux[FunK2, IsKind2, TypeK2[VoidK2]] = new Funk2Initial {}
  given terminal: Terminal.Aux[FunK2, IsKind2, TypeK2[UnitK2]] = new FunK2Terminal {}

  given cccTuple: Ccc.Aux[FunK2, Tuple2, FunK2, IsKind2, TypeK2[UnitK2]] = new Funk2CccTuple {}
  given cccConjunction: Ccc.Aux[FunK2, /\, FunK2, IsKind2, TypeK2[UnitK2]] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> Ccc.Aux[FunK2, f, FunK2, IsKind2, TypeK2[UnitK2]]](cccTuple)
  given cocartesianOppEither: Cartesian.Aux[Opp[FunK2], Either, IsKind2, TypeK2[VoidK2]] = new Funk2CocartesianEither {}
  given cocartesianEither: Cartesian.Aux[Dual[FunK2,*,*], Either, IsKind2, TypeK2[VoidK2]] =
    Dual.leibniz[FunK2].subst[[f[_,_]] =>> Cartesian.Aux[f[_,_], Either, IsKind2, TypeK2[VoidK2]]](cocartesianOppEither)
  given cocartesianDisjunction: Cocartesian.Aux[FunK2, \/, IsKind2, TypeK2[VoidK2]] =
    \/.unsafeLeibniz.subst[[f[_,_]] =>> Cocartesian.Aux[FunK2, f, IsKind2, TypeK2[VoidK2]]](cocartesianEither)
}

trait Funk2Implicits01 {
  given distributeConjDisj: Distributive.Aux[FunK2, IsKind2, /\, TypeK2[UnitK2], \/, TypeK2[VoidK2]] =
    =~~=.lower2[[f[_,_], g[_,_]] =>> Distributive.Aux[FunK2, IsKind2, f, TypeK2[UnitK2], g, TypeK2[VoidK2]]]
      .on(/\.unsafeLeibniz, \/.unsafeLeibniz)(FunK2.distributeTupleEither)
}

object FunK2Helpers:
  trait Funk2BifTuple extends Endobifunctor[FunK2, Tuple2]:
    def bimap[A, X, B, Y](left: FunK2[A, X], right: FunK2[B, Y]): FunK2[(A, B), (X, Y)] =
      FunK2(~~>.product.bimap(left.fn, right.fn))(using
        IsKind2.givenTuple(using left.kindA, right.kindA),
        IsKind2.givenTuple(using left.kindB, right.kindB)
      )

  trait Funk2BifEither extends Endobifunctor[FunK2, Either]:
    def bimap[A, X, B, Y](l: FunK2[A, X], r: FunK2[B, Y]): FunK2[Either[A, B], Either[X, Y]] =
      FunK2(~~>.coproduct.bimap(l.fn, r.fn))(using IsKind2.givenEither(using l.kindA, r.kindA), IsKind2.givenEither(using l.kindB, r.kindB))

  trait Funk2Subcat extends Distributive.Proto[FunK2, IsKind2, Tuple2, TypeK2[UnitK2], Either, TypeK2[VoidK2]]:
    def id[A](using A: IsKind2[A]): FunK2[A, A] = FunK2(~~>.id[A.Type])
    def andThen[A, B, C](ab: FunK2[A, B], bc: FunK2[B, C]): FunK2[A, C] =
      FunK2(~~>.andThen(ab.fn, IsKind2.injectivity(bc.kindA, ab.kindB).subst[[f[_,_]] =>> f ~~> bc.TypeB](bc.fn)))(using ab.kindA, bc.kindB)
    def cartesian:   Cartesian.Aux[FunK2, Tuple2, IsKind2, TypeK2[UnitK2]] = summon
    def cocartesian: Cocartesian.Aux[FunK2, Either, IsKind2, TypeK2[VoidK2]] = summon
    def distribute[A, B, C](using ia: IsKind2[A], ib: IsKind2[B], ic: IsKind2[C]): FunK2[(A, Either[B, C]), Either[(A, B), (A, C)]] =
      FunK2(~~>.distribute[ia.Type, ib.Type, ic.Type])(using IsKind2.givenTuple[A, Either[B, C]], IsKind2.givenEither[(A, B), (A, C)])

  trait Funk2Initial extends Initial.Proto[FunK2, IsKind2, TypeK2[VoidK2]]:
    lazy val subcat: Subcategory.Aux[FunK2, IsKind2] = summon
    lazy val TC: IsKind2[TypeK2[VoidK2]] = summon
    def initiate[A](using A: IsKind2[A]): FunK2[TypeK2[VoidK2], A] = FunK2(~~>.initiate[A.Type])

  class FunK2Terminal extends Terminal.Proto[FunK2, IsKind2, TypeK2[UnitK2]]:
    lazy val TC: IsKind2[TypeK2[UnitK2]] = summon
    lazy val subcat: Subcategory.Aux[Dual[FunK2,*,*], IsKind2] = Semicategory.dualSubcat[FunK2, IsKind2]
    def terminate[A](using A: IsKind2[A]): FunK2[A, TypeK2[UnitK2]] = FunK2(~~>.terminate[A.Type])

  trait Funk2CccTuple extends Ccc.Proto[FunK2, Tuple2, IsKind2, TypeK2[UnitK2], FunK2]:
    lazy val C: Subcat.Aux[FunK2, IsKind2] = summon
    lazy val bifunctor: Endobifunctor[FunK2, Tuple2] = summon
    def associate  [X, Y, Z](using ix: IsKind2[X], iy: IsKind2[Y], iz: IsKind2[Z]): FunK2[((X, Y), Z), (X, (Y, Z))] =
      FunK2(~~>.product.associate[ix.Type, iy.Type, iz.Type])(using
        IsKind2.givenTuple[(X, Y), Z],
        IsKind2.givenTuple[X, (Y, Z)]
      )
    def diassociate[X, Y, Z](using ix: IsKind2[X], iy: IsKind2[Y], iz: IsKind2[Z]): FunK2[(X, (Y, Z)), ((X, Y), Z)] =
      FunK2(~~>.product.diassociate[ix.Type, iy.Type, iz.Type])(using
        IsKind2.givenTuple[X, (Y, Z)],
        IsKind2.givenTuple[(X, Y), Z]
      )
    def fst[A, B](using ia: IsKind2[A], ib: IsKind2[B]): FunK2[(A, B), A] =
      FunK2(~~>.product.fst[ia.Type, ib.Type])(using IsKind2.givenTuple[A, B], ia)
    def snd[A, B](using ia: IsKind2[A], ib: IsKind2[B]): FunK2[(A, B), B] =
      FunK2(~~>.product.snd[ia.Type, ib.Type])(using IsKind2.givenTuple[A, B], ib)
    def diag[A](using ia: IsKind2[A]): FunK2[A, (A, A)] =
      FunK2(~~>.product.diag[ia.Type])(using ia, IsKind2.givenTuple(using ia, ia))
    def &&&[X, Y, Z](f: FunK2[X, Y], g: FunK2[X, Z]): FunK2[X, (Y, Z)] =
      FunK2(
        ~~>.product.merge(f.fn, IsKind2.injectivity(g.kindA, f.kindA).subst[[f[_,_]] =>> f ~~> g.TypeB](g.fn))
      )(using f.kindA, IsKind2.givenTuple(using f.kindB, g.kindB))
    def idl  [A](using ia: IsKind2[A]): FunK2[(TypeK2[UnitK2], A), A] =
      FunK2(~~>.product.idl[ia.Type])(using IsKind2.givenTuple[TypeK2[UnitK2], A], ia)
    def coidl[A](using ia: IsKind2[A]): FunK2[A, (TypeK2[UnitK2], A)] =
      FunK2(~~>.product.coidl[ia.Type])(using ia, IsKind2.givenTuple[TypeK2[UnitK2], A])
    def idr  [A](using ia: IsKind2[A]): FunK2[(A, TypeK2[UnitK2]), A] =
      FunK2(~~>.product.idr[ia.Type])(using IsKind2.givenTuple[A, TypeK2[UnitK2]], ia)
    def coidr[A](using ia: IsKind2[A]): FunK2[A, (A, TypeK2[UnitK2])] =
      FunK2(~~>.product.coidr[ia.Type])(using ia, IsKind2.givenTuple[A, TypeK2[UnitK2]])
    def braid[A, B](using ia: IsKind2[A], ib: IsKind2[B]): FunK2[(A, B), (B, A)] =
      FunK2(~~>.product.braid[ia.Type, ib.Type])(using IsKind2.givenTuple[A, B], IsKind2.givenTuple[B, A])
    def curry[A, B, C](f: FunK2[(A, B), C]): FunK2[A, FunK2[B, C]] = {
      given c: IsKind2.Aux[C, f.TypeB] = f.kindB
      val (ia, ib) = f.kindA.tuple[A, B]
      val fun = IsKind2.injectivity(f.kindA, IsKind2.givenTuple[A, B](using ia, ib)).subst[[f[_,_]] =>> f ~~> f.TypeB](f.fn)
      FunK2[ia.Type, [o,p] =>> ib.Type[o,p] => c.Type[o,p], A, FunK2[B, C]](~~>.product.curry(fun))(using ia, IsKind2.givenFunction[B, C](using ib, c))
    }
    def uncurry[A, B, C](f: FunK2[A, FunK2[B, C]]): FunK2[(A, B), C] = {
      given a: IsKind2.Aux[A, f.TypeA] = f.kindA
      val (ib, ic) = f.kindB.funk[B, C]
      val fun = IsKind2.injectivity(f.kindB, IsKind2.givenFunction[B, C](using ib, ic)).subst[[f[_,_]] =>> f.TypeA ~~> f](f.fn)
      FunK2[[o,p] =>> (a.Type[o,p], ib.Type[o,p]), ic.Type, (A, B), C](~~>.product.uncurry(fun))(using IsKind2.givenTuple[A, B](using a, ib), ic)
    }

  trait Funk2CocartesianEither extends Cartesian.Proto[Opp[FunK2], Either, IsKind2, TypeK2[VoidK2]]:
    lazy val bifunctor = Exobifunctor.oppEndobifunctor[FunK2, Either]
    lazy val C = Semicategory.oppSubcat[FunK2, IsKind2]
    def associate  [X, Y, Z](using ix: IsKind2[X], iy: IsKind2[Y], iz: IsKind2[Z]): FunK2[Either[X, Either[Y, Z]], Either[Either[X, Y], Z]] =
      FunK2(~~>.coproduct.associate[ix.Type, iy.Type, iz.Type])(using
        IsKind2.givenEither[X, Either[Y, Z]],
        IsKind2.givenEither[Either[X, Y], Z]
      )
    def diassociate[X, Y, Z](using ix: IsKind2[X], iy: IsKind2[Y], iz: IsKind2[Z]): FunK2[Either[Either[X, Y], Z], Either[X, Either[Y, Z]]] =
      FunK2(~~>.coproduct.diassociate[ix.Type, iy.Type, iz.Type])(using
        IsKind2.givenEither[Either[X, Y], Z],
        IsKind2.givenEither[X, Either[Y, Z]]
      )
    def fst[A, B](using ia: IsKind2[A], ib: IsKind2[B]): FunK2[A, Either[A, B]] =
      FunK2(~~>.coproduct.inl[ia.Type, ib.Type])(using ia, IsKind2.givenEither[A, B])
    def snd[A, B](using ia: IsKind2[A], ib: IsKind2[B]): FunK2[B, Either[A, B]] =
      FunK2(~~>.coproduct.inr[ia.Type, ib.Type])(using ib, IsKind2.givenEither[A, B])
    def diag[A](using ia: IsKind2[A]): FunK2[Either[A, A], A] =
      FunK2(~~>.coproduct.codiag[ia.Type])(using IsKind2.givenEither[A, A], ia)
    def &&&[X, Y, Z](f: FunK2[Y, X], g: FunK2[Z, X]): FunK2[Either[Y, Z], X] =
      FunK2(~~>.coproduct.split(f.fn, IsKind2.injectivity(g.kindB, f.kindB).subst[[f[_,_]] =>> g.TypeA ~~> f](g.fn))
      )(using IsKind2.givenEither(using f.kindA, g.kindA), f.kindB)
    def idl  [A](using ia: IsKind2[A]): FunK2[A, Either[TypeK2[VoidK2], A]] =
      FunK2(~~>.coproduct.idl[ia.Type])(using ia, IsKind2.givenEither[TypeK2[VoidK2], A])
    def coidl[A](using ia: IsKind2[A]): FunK2[Either[TypeK2[VoidK2], A], A] =
      FunK2(~~>.coproduct.coidl[ia.Type])(using IsKind2.givenEither[TypeK2[VoidK2], A], ia)
    def idr  [A](using ia: IsKind2[A]): FunK2[A, Either[A, TypeK2[VoidK2]]] =
      FunK2(~~>.coproduct.idr[ia.Type])(using ia, IsKind2.givenEither[A, TypeK2[VoidK2]])
    def coidr[A](using ia: IsKind2[A]): FunK2[Either[A, TypeK2[VoidK2]], A] =
      FunK2(~~>.coproduct.coidr[ia.Type])(using IsKind2.givenEither[A, TypeK2[VoidK2]], ia)
    def braid[A, B](using ia: IsKind2[A], ib: IsKind2[B]): FunK2[Either[B, A], Either[A, B]] =
      FunK2(~~>.coproduct.braid[ib.Type, ia.Type])(using IsKind2.givenEither[B, A], IsKind2.givenEither[A, B])

end FunK2Helpers
