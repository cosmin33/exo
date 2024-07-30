package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax.*

trait FunH[A, B]:
  type TypeA[_[_]]
  type TypeB[_[_]]
  def kindA: IsHKind.Aux[A, TypeA]
  def kindB: IsHKind.Aux[B, TypeB]
  def fn: TypeA ≈> TypeB
  def unapply(using ia: IsHKind[A], ib: IsHKind[B]): ia.Type ≈> ib.Type =
    IsHK.lower2(IsHKind.injectivity(kindA, ia), IsHKind.injectivity(kindB, ib))(fn)

object FunH extends FunhImplicits {
  type Aux[A, B, F[_[_]], G[_[_]]] = FunH[A, B] { type TypeA[f[_]] = F[f]; type TypeB[f[_]] = G[f] }
  def apply[F[_[_]], G[_[_]], A, B](f: F ≈> G)(using a: IsHKind.Aux[A, F], b: IsHKind.Aux[B, G]): FunH[A, B] =
    new FunH[A, B] { type TypeA[f[_]] = F[f]; type TypeB[f[_]] = G[f]; val (kindA, kindB, fn) = (a, b, f) }

  def isoFunHUnapply[A, B](i: IsoFunH[A, B])(using a: IsHKind[A], b: IsHKind[B]): a.Type <≈> b.Type =
    <≈>.unsafe(i.to.unapply, i.from.unapply)

  given isoFunHCanonic   [A, B](using a: IsHKind[A], b: IsHKind[B]): (FunH[A, B] <=> (a.Type ≈> b.Type)) = Iso.unsafe(_.unapply, apply)
  given isoIsoFunHCanonic[A, B](using a: IsHKind[A], b: IsHKind[B]): (IsoFunH[A, B] <=> (a.Type <≈> b.Type)) =
    Iso.unsafe(i => <≈>.unsafe(i.to.unapply, i.from.unapply), i => Iso.unsafe(apply(i.to), apply(i.from)))

}

import FunHHelpers.*

trait FunhImplicits extends FunhImplicits01 {
  given bifunctorTuple:  Endobifunctor[FunH, Tuple2] = new FunhBifTuple {}
  given bifunctorEither: Endobifunctor[FunH, Either] = new FunhBifEither {}

  given distributeTupleEither: Distributive.Aux[FunH, IsHKind, Tuple2, TypeHK[UnitHK], Either, TypeHK[VoidHK]] = new FunhSubcat {}

  given initial: Initial.Aux[FunH, IsHKind, TypeHK[VoidHK]] = new FunhInitial {}
  given terminal: Terminal.Aux[FunH, IsHKind, TypeHK[UnitHK]] = new FunhTerminal {}

  given cccTuple: Ccc.Aux[FunH, Tuple2, IsHKind, TypeHK[UnitHK], FunH] = new FunhCccTuple {}
  given cccConjunction: Ccc.Aux[FunH, /\, IsHKind, TypeHK[UnitHK], FunH] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> Ccc.Aux[FunH, f, IsHKind, TypeHK[UnitHK], FunH]](cccTuple)
  given cocartesianOppEither: Cartesian.Aux[Opp[FunH]#l, Either, IsHKind, TypeHK[VoidHK]] = new FunhCocartesianEither {}
  given cocartesianEither: Cartesian.Aux[Dual[FunH,*,*], Either, IsHKind, TypeHK[VoidHK]] =
    Dual.leibniz[FunH].subst[[f[_,_]] =>> Cartesian.Aux[f[_,_], Either, IsHKind, TypeHK[VoidHK]]](cocartesianOppEither)
  given cocartesianDisjunction: Cocartesian.Aux[FunH, \/, IsHKind, TypeHK[VoidHK]] =
    \/.unsafeLeibniz.subst[[f[_,_]] =>> Cocartesian.Aux[FunH, f, IsHKind, TypeHK[VoidHK]]](cocartesianEither)
}

trait FunhImplicits01 {
  given distributeConjDisj: Distributive.Aux[FunH, IsHKind, /\, TypeHK[UnitHK], \/, TypeHK[VoidHK]] =
    =~~=.lower2[[f[_,_], g[_,_]] =>> Distributive.Aux[FunH, IsHKind, f, TypeHK[UnitHK], g, TypeHK[VoidHK]]]
      .on(/\.unsafeLeibniz, \/.unsafeLeibniz)(FunH.distributeTupleEither)
}

object FunHHelpers:

  trait FunhBifTuple extends Endobifunctor[FunH, Tuple2]:
    def bimap[A, X, B, Y](left: FunH[A, X], right: FunH[B, Y]): FunH[(A, B), (X, Y)] =
      FunH(≈>.product.bimap(left.fn, right.fn))(using
        IsHKind.givenTuple(using left.kindA, right.kindA),
        IsHKind.givenTuple(using left.kindB, right.kindB)
      )

  trait FunhBifEither extends Endobifunctor[FunH, Either]:
    def bimap[A, X, B, Y](l: FunH[A, X], r: FunH[B, Y]): FunH[Either[A, B], Either[X, Y]] =
      FunH(≈>.coproduct.bimap(l.fn, r.fn))(using IsHKind.givenEither(using l.kindA, r.kindA), IsHKind.givenEither(using l.kindB, r.kindB))

  trait FunhSubcat extends Distributive.Proto[FunH, IsHKind, Tuple2, TypeHK[UnitHK], Either, TypeHK[VoidHK]]:
    def id[A](using A: IsHKind[A]): FunH[A, A] = FunH(≈>.id[A.Type])
    def andThen[A, B, C](ab: FunH[A, B], bc: FunH[B, C]): FunH[A, C] =
      FunH(≈>.andThen(ab.fn, IsHKind.injectivity(bc.kindA, ab.kindB).subst[[f[_[_]]] =>> f ≈> bc.TypeB](bc.fn)))(using ab.kindA, bc.kindB)
    def cartesian:   Cartesian.Aux[FunH, Tuple2, IsHKind, TypeHK[UnitHK]] = summon
    def cocartesian: Cocartesian.Aux[FunH, Either, IsHKind, TypeHK[VoidHK]] = summon
    def distribute[A, B, C](using ia: IsHKind[A], ib: IsHKind[B], ic: IsHKind[C]): FunH[(A, Either[B, C]), Either[(A, B), (A, C)]] =
      FunH(≈>.distribute[ia.Type, ib.Type, ic.Type])(using IsHKind.givenTuple[A, Either[B, C]], IsHKind.givenEither[(A, B), (A, C)])

  trait FunhInitial extends Initial.Proto[FunH, IsHKind, TypeHK[VoidHK]]:
    def subcat: Subcategory.Aux[FunH, IsHKind] = summon
    def TC: IsHKind[TypeHK[VoidHK]] = summon
    def initiate[A](using A: IsHKind[A]): FunH[TypeHK[VoidHK], A] = FunH(≈>.initiate[A.Type])

  trait FunhTerminal extends Terminal.Proto[FunH, IsHKind, TypeHK[UnitHK]]:
    def TC: IsHKind[TypeHK[UnitHK]] = summon
    def subcat: Subcategory.Aux[Dual[FunH,*,*], IsHKind] = summon
    def terminate[A](using A: IsHKind[A]): FunH[A, TypeHK[UnitHK]] = FunH(≈>.terminate[A.Type])

  trait FunhCccTuple extends Ccc.Proto[FunH, Tuple2, IsHKind, TypeHK[UnitHK], FunH]:
    def C: Subcat.Aux[FunH, IsHKind] = summon
    def bifunctor: Endobifunctor[FunH, Tuple2] = summon
    def associate  [X, Y, Z](using ix: IsHKind[X], iy: IsHKind[Y], iz: IsHKind[Z]): FunH[((X, Y), Z), (X, (Y, Z))] =
      FunH(≈>.product.associate[ix.Type, iy.Type, iz.Type])(using
        IsHKind.givenTuple[(X, Y), Z],
        IsHKind.givenTuple[X, (Y, Z)]
      )
    def diassociate[X, Y, Z](using ix: IsHKind[X], iy: IsHKind[Y], iz: IsHKind[Z]): FunH[(X, (Y, Z)), ((X, Y), Z)] =
      FunH(≈>.product.diassociate[ix.Type, iy.Type, iz.Type])(using
        IsHKind.givenTuple[X, (Y, Z)],
        IsHKind.givenTuple[(X, Y), Z]
      )
    def fst[A, B](using ia: IsHKind[A], ib: IsHKind[B]): FunH[(A, B), A] =
      FunH(≈>.product.fst[ia.Type, ib.Type])(using IsHKind.givenTuple[A, B], ia)
    def snd[A, B](using ia: IsHKind[A], ib: IsHKind[B]): FunH[(A, B), B] =
      FunH(≈>.product.snd[ia.Type, ib.Type])(using IsHKind.givenTuple[A, B], ib)
    def diag[A](using ia: IsHKind[A]): FunH[A, (A, A)] =
      FunH(≈>.product.diag[ia.Type])(using ia, IsHKind.givenTuple(using ia, ia))
    def &&&[X, Y, Z](f: FunH[X, Y], g: FunH[X, Z]): FunH[X, (Y, Z)] =
      FunH(
        ≈>.product.merge(f.fn, IsHKind.injectivity(g.kindA, f.kindA).subst[[f[_[_]]] =>> f ≈> g.TypeB](g.fn))
      )(using f.kindA, IsHKind.givenTuple(using f.kindB, g.kindB))
    def idl  [A](using ia: IsHKind[A]): FunH[(TypeHK[UnitHK], A), A] =
      FunH(≈>.product.idl[ia.Type])(using IsHKind.givenTuple[TypeHK[UnitHK], A], ia)
    def coidl[A](using ia: IsHKind[A]): FunH[A, (TypeHK[UnitHK]                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               , A)] =
      FunH(≈>.product.coidl[ia.Type])(using ia, IsHKind.givenTuple[TypeHK[UnitHK], A])
    def idr  [A](using ia: IsHKind[A]): FunH[(A, TypeHK[UnitHK]), A] =
      FunH(≈>.product.idr[ia.Type])(using IsHKind.givenTuple[A, TypeHK[UnitHK]], ia)
    def coidr[A](using ia: IsHKind[A]): FunH[A, (A, TypeHK[UnitHK])] =
      FunH(≈>.product.coidr[ia.Type])(using ia, IsHKind.givenTuple[A, TypeHK[UnitHK]])
    def braid[A, B](using ia: IsHKind[A], ib: IsHKind[B]): FunH[(A, B), (B, A)] =
      FunH(≈>.product.braid[ia.Type, ib.Type])(using IsHKind.givenTuple[A, B], IsHKind.givenTuple[B, A])
    def curry[A, B, C](f: FunH[(A, B), C]): FunH[A, FunH[B, C]] = {
      given c: IsHKind.Aux[C, f.TypeB] = f.kindB
      val (ia, ib) = f.kindA.tuple[A, B]
      val fun = IsHKind.injectivity(f.kindA, IsHKind.givenTuple[A, B](using ia, ib)).subst[[f[_[_]]] =>> f ≈> f.TypeB](f.fn)
      FunH[ia.Type, [o[_]] =>> ib.Type[o] => c.Type[o], A, FunH[B, C]](≈>.product.curry(fun))(using ia, IsHKind.givenFunction[B, C](using ib, c))
    }
    def uncurry[A, B, C](f: FunH[A, FunH[B, C]]): FunH[(A, B), C] = {
      given a: IsHKind.Aux[A, f.TypeA] = f.kindA
      val (ib, ic) = f.kindB.function[B, C]
      val fun = IsHKind.injectivity(f.kindB, IsHKind.givenFunction[B, C](using ib, ic)).subst[[f[_[_]]] =>> f.TypeA ≈> f](f.fn)
      FunH[[o[_]] =>> (a.Type[o], ib.Type[o]), ic.Type, (A, B), C](≈>.product.uncurry(fun))(using IsHKind.givenTuple[A, B](using a, ib), ic)
    }

  trait FunhCocartesianEither extends Cartesian.Proto[Opp[FunH]#l, Either, IsHKind, TypeHK[VoidHK]]:
    def bifunctor = Exobifunctor.oppEndobifunctor[FunH, Either]
    def C = Semicategory.oppSubcat[FunH, IsHKind]
    def associate  [X, Y, Z](using ix: IsHKind[X], iy: IsHKind[Y], iz: IsHKind[Z]): FunH[Either[X, Either[Y, Z]], Either[Either[X, Y], Z]] =
      FunH(≈>.coproduct.associate[ix.Type, iy.Type, iz.Type])(using
        IsHKind.givenEither[X, Either[Y, Z]],
        IsHKind.givenEither[Either[X, Y], Z]
      )
    def diassociate[X, Y, Z](using ix: IsHKind[X], iy: IsHKind[Y], iz: IsHKind[Z]): FunH[Either[Either[X, Y], Z], Either[X, Either[Y, Z]]] =
      FunH(≈>.coproduct.diassociate[ix.Type, iy.Type, iz.Type])(using
        IsHKind.givenEither[Either[X, Y], Z],
        IsHKind.givenEither[X, Either[Y, Z]]
      )
    def fst[A, B](using ia: IsHKind[A], ib: IsHKind[B]): FunH[A, Either[A, B]] =
      FunH(≈>.coproduct.inl[ia.Type, ib.Type])(using ia, IsHKind.givenEither[A, B])
    def snd[A, B](using ia: IsHKind[A], ib: IsHKind[B]): FunH[B, Either[A, B]] =
      FunH(≈>.coproduct.inr[ia.Type, ib.Type])(using ib, IsHKind.givenEither[A, B])
    def diag[A](using ia: IsHKind[A]): FunH[Either[A, A], A] =
      FunH(≈>.coproduct.codiag[ia.Type])(using IsHKind.givenEither[A, A], ia)
    def &&&[X, Y, Z](f: FunH[Y, X], g: FunH[Z, X]): FunH[Either[Y, Z], X] =
      FunH(≈>.coproduct.split(f.fn, IsHKind.injectivity(g.kindB, f.kindB).subst[[f[_[_]]] =>> g.TypeA ≈> f](g.fn))
      )(using IsHKind.givenEither(using f.kindA, g.kindA), f.kindB)
    def idl  [A](using ia: IsHKind[A]): FunH[A, Either[TypeHK[VoidHK], A]] =
      FunH(≈>.coproduct.idl[ia.Type])(using ia, IsHKind.givenEither[TypeHK[VoidHK], A])
    def coidl[A](using ia: IsHKind[A]): FunH[Either[TypeHK[VoidHK], A], A] =
      FunH(≈>.coproduct.coidl[ia.Type])(using IsHKind.givenEither[TypeHK[VoidHK], A], ia)
    def idr  [A](using ia: IsHKind[A]): FunH[A, Either[A, TypeHK[VoidHK]]] =
      FunH(≈>.coproduct.idr[ia.Type])(using ia, IsHKind.givenEither[A, TypeHK[VoidHK]])
    def coidr[A](using ia: IsHKind[A]): FunH[Either[A, TypeHK[VoidHK]], A] =
      FunH(≈>.coproduct.coidr[ia.Type])(using IsHKind.givenEither[A, TypeHK[VoidHK]], ia)
    def braid[A, B](using ia: IsHKind[A], ib: IsHKind[B]): FunH[Either[B, A], Either[A, B]] =
      FunH(≈>.coproduct.braid[ib.Type, ia.Type])(using IsHKind.givenEither[B, A], IsHKind.givenEither[A, B])

end FunHHelpers
