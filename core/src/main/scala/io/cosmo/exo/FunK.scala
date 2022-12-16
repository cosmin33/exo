package io.cosmo.exo

import io.cosmo.exo.Iso.{HasIso, HasIsoK}
import io.cosmo.exo.categories.Cartesian.Aux
import io.cosmo.exo.categories.data.EvidenceCat
import io.cosmo.exo.categories.{Cartesian, Ccc, Cocartesian, Distributive, Dual, DualModule, Endobifunctor, Initial, Monoidal, Opp, Subcat, Terminal, Trivial}
import io.cosmo.exo.categories.functors.{Endobifunctor, Exo, Exofunctor}
import io.cosmo.exo.evidence.{===, =~=, IsK}
import io.cosmo.exo.evidence.internal.Unsafe
import io.cosmo.exo.typeclasses.{HasTc, TypeK}

sealed trait IsKind[A] {
  type Type[_]
}
object IsKind {
  type Aux[A, T[_]] = IsKind[A] { type Type[a] = T[a] }
  def apply[A](implicit a: IsKind[A]): IsKind.Aux[A, a.Type] = a

  implicit def impl[F[_]]: IsKind.Aux[TypeK[F], F] = new IsKind[TypeK[F]] { type Type[a] = F[a] }

  implicit def pair2[A, B](implicit l: IsKind[A], r: IsKind[B]): IsKind.Aux[(A, B), λ[α => (l.Type[α], r.Type[α])]] =
    new IsKind[(A, B)] { type Type[α] = (l.Type[α], r.Type[α]) }
  implicit def pair2_[A, B](implicit l: IsKind[A], r: IsKind[B]): IsKind.Aux[A /\ B, λ[α => l.Type[α] /\ r.Type[α]]] =
    new IsKind[A /\ B] { type Type[α] = l.Type[α] /\ r.Type[α] }

  implicit def either2[A, B](implicit a: IsKind[A], b: IsKind[B]): IsKind.Aux[Either[A, B], λ[α => Either[a.Type[α], b.Type[α]]]] =
    new IsKind[Either[A, B]] { type Type[α] = Either[a.Type[α], b.Type[α]] }
  implicit def either2_[A, B](implicit a: IsKind[A], b: IsKind[B]): IsKind.Aux[A \/ B, λ[α => \/[a.Type[α], b.Type[α]]]] =
    new IsKind[A \/ B] { type Type[α] = \/[a.Type[α], b.Type[α]] }

  def injectivity[A, B](ia: IsKind[A], ib: IsKind[B])(implicit eq: IsKind[A] === IsKind[B]): ia.Type =~= ib.Type =
    Unsafe.isK

  def isoInjectivity[A, B](implicit ia: IsKind[A], ib: IsKind[B]): (IsKind[A] === IsKind[B]) <=> (ia.Type =~= ib.Type) =
    Iso.unsafe(_ => Unsafe.isK, _=> Unsafe.is)
}

sealed trait NestK[A, B]
object NestK {
  implicit def isKind[A, B](implicit a: IsKind[A], b: IsKind[B]): IsKind.Aux[NestK[A, B], λ[x => a.Type[b.Type[x]]]] =
    new IsKind[NestK[A, B]] { type Type[x] = a.Type[b.Type[x]] }
}

trait FunK[A, B] {
  type TypeA[_]
  type TypeB[_]
  def kindA: IsKind.Aux[A, TypeA]
  def kindB: IsKind.Aux[B, TypeB]
  def fn: TypeA ~> TypeB
  def unapply[F[_], G[_]](implicit
    ia: IsKind.Aux[A, F],
    ib: IsKind.Aux[B, G]
  ): F ~> G = IsK.lower2(IsKind.injectivity(kindA, ia), IsKind.injectivity(kindB, ib))(fn)
}

/** Natural transformation: besides being a FunK this one asks for underlying types to have functors in Function1, also some laws */
trait NatK[A, B] extends FunK[A, B] {
  def functorA: Exo.CovF[TypeA]
  def functorB: Exo.CovF[TypeB]
}

object FunK {
  type Aux[A, B, F[_], G[_]] = FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a] }
  def apply[F[_], G[_]](f: F ~> G): FunK.Aux[TypeK[F], TypeK[G], F, G] = FunK.from(f)(IsKind[TypeK[F]], IsKind[TypeK[G]])
  def from[F[_], G[_], A, B](f: F ~> G)(a: IsKind.Aux[A, F], b: IsKind.Aux[B, G]): FunK.Aux[A, B, F, G] =
    new FunK[A, B] {
      type TypeA[a] = F[a]
      type TypeB[a] = G[a]
      val kindA = a
      val kindB = b
      val fn =  f
    }

  type TypeclassedFunK[TC[_[_]], A, B] = EvidenceCat[HasTc[TC, *], A, B] /\ FunK[A, B]
  type FunctorFunK[A, B] = TypeclassedFunK[Exo.CovF, A, B]

  def isoFunKUnapply[A, B, F[_], G[_]](i: IsoFunK[A, B])(implicit a: IsKind.Aux[A, F], b: IsKind.Aux[B, G]): F <~> G =
    <~>.unsafe(i.to.unapply, i.from.unapply)

  implicit def impIsoFunK[F[_], G[_]](implicit i: F <~> G): Iso[FunK, TypeK[F], TypeK[G]] = i.isoWith[Iso[FunK, TypeK[F], TypeK[G]]]

  implicit def isoToFun[F[_], G[_]]: FunK[TypeK[F], TypeK[G]] <=> (F ~> G) = Iso.unsafe(_.unapply, apply)
  implicit def isoKIso[F[_], G[_]]: IsoFunK[TypeK[F], TypeK[G]] <=> (F <~> G) =
    Iso.unsafe(i => <~>.unsafe(i.to.unapply, i.from.unapply), i => Iso.unsafe(apply(i.to), apply(i.from)))

  import io.cosmo.exo.FunKHelpers._

  implicit def subcat: Distributive.Aux[FunK, IsKind, (*, *), TypeK[UnitK], Either, TypeK[VoidK]]
    with Initial.Aux[FunK, IsKind, TypeK[VoidK]]
    with Terminal.Aux[FunK, IsKind, TypeK[UnitK]]
  = new FunkSubcat {}

  implicit def bifunctorTuple: Endobifunctor[FunK, Tuple2] = new FunkBifTuple {}

  implicit def bifunctorEither: Endobifunctor[FunK, Either] = new FunkBifEither {}

  implicit def cartesian: Cartesian.Aux[FunK, Tuple2, IsKind, TypeK[UnitK]] = new FunkCartesianTuple {}
  implicit def cocartesian: Cartesian.Aux[Dual[FunK,*,*], Either, IsKind, TypeK[VoidK]] =
    Dual.leibniz[FunK].subst[Cartesian.Aux[*[_,_], Either, IsKind, TypeK[VoidK]]](cocartesianOpp)

  def cocartesianOpp: Cartesian.Aux[Opp[FunK]#l, Either, IsKind, TypeK[VoidK]] = new FunkCocartesianEither {}


  implicit def compositionFunctor: Endobifunctor[FunK, NestK] =
    new Endobifunctor[FunK, NestK] {
      def bimap[A, X, B, Y](l: FunK[A, X], r: FunK[B, Y]): FunK[NestK[A, B], NestK[X, Y]] = ??? //FunK.from(~>.composition.bimap(l.fn, r.fn))
    }


  implicit def compositionMonoidal: Monoidal.Aux[FunK, NestK, IsKind, TypeK[λ[a => a]]] =
    new Monoidal[FunK, NestK] {
      type TC[a] = IsKind[a]
      type Id = TypeK[λ[a => a]]
      def C: Subcat.Aux[FunK, IsKind] = implicitly
      def bifunctor: Endobifunctor[FunK, NestK] = implicitly
      def idl  [A](implicit ia: TC[A]) = FunK.from(~>.composition.idl[ia.Type])(NestK.isKind(IsKind[TypeK[cats.Id]], ia), ia)
      def coidl[A](implicit ia: TC[A]) = FunK.from(~>.composition.coidl[ia.Type])(ia, NestK.isKind(IsKind[TypeK[cats.Id]], ia))
      def idr  [A](implicit ia: TC[A]) = FunK.from(~>.composition.idr[ia.Type])(NestK.isKind(ia, IsKind[TypeK[cats.Id]]), ia)
      def coidr[A](implicit ia: TC[A]) = FunK.from(~>.composition.coidr[ia.Type])(ia, NestK.isKind(ia, IsKind[TypeK[cats.Id]]))
      def associate  [X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]) = FunK.from(
        ~>.composition.associate[ix.Type, iy.Type, iz.Type])(
        NestK.isKind(NestK.isKind(ix, iy), iz),
        NestK.isKind(ix, NestK.isKind(iy, iz))
      )
      def diassociate[X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]) = FunK.from(
        ~>.composition.diassociate[ix.Type, iy.Type, iz.Type])(
        NestK.isKind(ix, NestK.isKind(iy, iz)),
        NestK.isKind(NestK.isKind(ix, iy), iz)
      )
    }

}

private[exo] object FunKHelpers {
  trait FunkSubcat extends Distributive[FunK, Tuple2, Either] with Initial[FunK]  with Terminal[FunK] with Ccc[FunK] {
    type TC[a] = IsKind[a]
    type ProductId = TypeK[UnitK]
    type ⨂[a,b] = (a, b)
    type SumId = TypeK[VoidK]
    type ⨁[a,b] = Either[a, b]
    type Initial = TypeK[VoidK]
    def initialTC = IsKind[TypeK[VoidK]]
    def initiate[A](implicit ia: IsKind[A]): FunK[TypeK[VoidK], A] =
      FunK.from(~>.initiate[ia.Type])(IsKind[TypeK[VoidK]], ia)
    type Terminal = TypeK[UnitK]
    def terminalTC = IsKind[TypeK[UnitK]]
    def terminate[A](implicit ia: IsKind[A]): FunK[A, TypeK[UnitK]] =
      FunK.from(~>.terminate[ia.Type])(ia, IsKind[TypeK[UnitK]])
    def cartesian = implicitly
    def cocartesian = implicitly

    type |->[A, B] = FunK[A, B]
    type ⊙[A, B] = (A, B)
    def curry[A, B, C](f: FunK[(A, B), C]): FunK[A, FunK[B, C]] = {
      val f1: f.TypeA ~> f.TypeB = f.fn
      val x1: IsKind.Aux[(A, B), f.TypeA] = f.kindA
//      val x2 = IsKind.pair2()
      //val f2 = ~>.curry(f.fn)
//      FunK.from()
      ???
    }
    def uncurry[A, B, C](f: FunK[A, FunK[B, C]]): FunK[(A, B), C] = ???

    def id[A](implicit ia: IsKind[A]): FunK[A, A] = FunK.from(~>.id[ia.Type])(ia, ia)
    def andThen[A, B, C](ab: FunK[A, B], bc: FunK[B, C]): FunK[A, C] =
      FunK.from(~>.andThen(ab.fn, IsKind.injectivity(bc.kindA, ab.kindB).subst[λ[f[_] => f ~> bc.TypeB]](bc.fn)))(ab.kindA, bc.kindB)
    def distribute[A, B, C](implicit ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): FunK[A ⨂ (B ⨁ C), (A ⨂ B) ⨁ (A ⨂ C)] =
      FunK.from(
        ~>.distribute[ia.Type, ib.Type, ic.Type])(
        IsKind.pair2(ia, IsKind.either2(ib, ic)),
        IsKind.either2(IsKind.pair2(ia, ib), IsKind.pair2(ia, ic))
      )
  }

  trait FunkBifTuple extends Endobifunctor[FunK, Tuple2] {
    def bimap[A, X, B, Y](left: FunK[A, X], right: FunK[B, Y]): FunK[(A, B), (X, Y)] =
      FunK.from(
        ~>.product.bimap(left.fn, right.fn))(
        IsKind.pair2(left.kindA, right.kindA),
        IsKind.pair2(left.kindB, right.kindB)
      )
  }

  trait FunkBifEither extends Endobifunctor[FunK, Either] {
    def bimap[A, X, B, Y](l: FunK[A, X], r: FunK[B, Y]): FunK[Either[A, B], Either[X, Y]] =
      FunK.from(~>.coproduct.bimap(l.fn, r.fn))(IsKind.either2(l.kindA, r.kindA), IsKind.either2(l.kindB, r.kindB))
  }

  trait FunkCartesianTuple extends Cartesian[FunK, Tuple2] {
    type Id = TypeK[UnitK]
    type TC[a] = IsKind[a]
    def C: Subcat.Aux[FunK, IsKind] = implicitly
    def bifunctor: Endobifunctor[FunK, Tuple2] = implicitly
    def fst[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), A] =
      FunK.from(~>.product.fst[ia.Type, ib.Type])(IsKind.pair2(ia, ib), ia)
    def snd[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), B] =
      FunK.from(~>.product.snd[ia.Type, ib.Type])(IsKind.pair2(ia, ib), ib)
    def diag[A](implicit ia: IsKind[A]): FunK[A, (A, A)] =
      FunK.from(~>.product.diag[ia.Type])(ia, IsKind.pair2(ia, ia))
    def &&&[X, Y, Z](f: FunK[X, Y], g: FunK[X, Z]): FunK[X, (Y, Z)] =
      FunK.from(
        ~>.product.merge(f.fn, IsKind.injectivity(g.kindA, f.kindA).subst[λ[f[_] => f ~> g.TypeB]](g.fn))
      )(f.kindA, IsKind.pair2(f.kindB, g.kindB))
    def idl  [A](implicit ia: IsKind[A]): FunK[(TypeK[UnitK], A), A] =
      FunK.from(~>.product.idl[ia.Type])(IsKind.pair2(IsKind[TypeK[UnitK]], ia), ia)
    def coidl[A](implicit ia: IsKind[A]): FunK[A, (TypeK[UnitK], A)] =
      FunK.from(~>.product.coidl[ia.Type])(ia, IsKind.pair2(IsKind[TypeK[UnitK]], ia))
    def idr  [A](implicit ia: IsKind[A]): FunK[(A, TypeK[UnitK]), A] =
      FunK.from(~>.product.idr[ia.Type])(IsKind.pair2(ia, IsKind[TypeK[UnitK]]), ia)
    def coidr[A](implicit ia: IsKind[A]): FunK[A, (A, TypeK[UnitK])] =
      FunK.from(~>.product.coidr[ia.Type])(ia, IsKind.pair2(ia, IsKind[TypeK[UnitK]]))
    def braid[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), (B, A)] =
      FunK.from(~>.product.braid[ia.Type, ib.Type])(IsKind.pair2(ia, ib), IsKind.pair2(ib, ia))
    def associate  [X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[((X, Y), Z), (X, (Y, Z))] =
      FunK.from(
        ~>.product.associate[ix.Type, iy.Type, iz.Type])(
        IsKind.pair2(IsKind.pair2(ix, iy), iz),
        IsKind.pair2(ix, IsKind.pair2(iy, iz))
      )
    def diassociate[X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[(X, (Y, Z)), ((X, Y), Z)] =
      FunK.from(
        ~>.product.diassociate[ix.Type, iy.Type, iz.Type])(
        IsKind.pair2(ix, IsKind.pair2(iy, iz)),
        IsKind.pair2(IsKind.pair2(ix, iy), iz)
      )
  }

  trait FunkCocartesianEither extends Cartesian[Opp[FunK]#l, Either] {
    type Id = TypeK[VoidK]
    type TC[a] = IsKind[a]
    def bifunctor = DualModule.oppEndobifunctor(Endobifunctor[FunK, Either])
    def C = DualModule.oppSubcat(implicitly[Subcat.Aux[FunK, IsKind]])
    def fst[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[A, Either[A, B]] =
      FunK.from(~>.coproduct.inl[ia.Type, ib.Type])(ia, IsKind.either2(ia, ib))
    def snd[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[B, Either[A, B]] =
      FunK.from(~>.coproduct.inr[ia.Type, ib.Type])(ib, IsKind.either2(ia, ib))
    def diag[A](implicit ia: IsKind[A]): FunK[Either[A, A], A] =
      FunK.from(~>.coproduct.codiag[ia.Type])(IsKind.either2(ia, ia), ia)
    def &&&[X, Y, Z](f: FunK[Y, X], g: FunK[Z, X]): FunK[Either[Y, Z], X] =
    FunK.from(
      ~>.coproduct.split(f.fn, IsKind.injectivity(g.kindB, f.kindB).subst[λ[f[_] => g.TypeA ~> f]](g.fn)))(
      IsKind.either2(f.kindA, g.kindA),
      f.kindB
    )
    def idl  [A](implicit ia: IsKind[A]): FunK[A, Either[TypeK[VoidK], A]] =
      FunK.from(~>.coproduct.idl[ia.Type])(ia, IsKind.either2(IsKind[TypeK[VoidK]], ia))
    def coidl[A](implicit ia: IsKind[A]): FunK[Either[TypeK[VoidK], A], A] =
      FunK.from(~>.coproduct.coidl[ia.Type])(IsKind.either2(IsKind[TypeK[VoidK]], ia), ia)
    def idr  [A](implicit ia: IsKind[A]): FunK[A, Either[A, TypeK[VoidK]]] =
      FunK.from(~>.coproduct.idr[ia.Type])(ia, IsKind.either2(ia, IsKind[TypeK[VoidK]]))
    def coidr[A](implicit ia: IsKind[A]): FunK[Either[A, TypeK[VoidK]], A] =
      FunK.from(~>.coproduct.coidr[ia.Type])(IsKind.either2(ia, IsKind[TypeK[VoidK]]), ia)
    def braid[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[Either[B, A], Either[A, B]] =
      FunK.from(~>.coproduct.braid[ib.Type, ia.Type])(IsKind.either2(ib, ia), IsKind.either2(ia, ib))
    def associate  [X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[X, Either[Y, Z]], Either[Either[X, Y], Z]] =
      FunK.from(
        ~>.coproduct.associate[ix.Type, iy.Type, iz.Type])(
        IsKind.either2(ix, IsKind.either2(iy, iz)),
        IsKind.either2(IsKind.either2(ix, iy), iz)
      )
    def diassociate[X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[Either[X, Y], Z], Either[X, Either[Y, Z]]] =
      FunK.from(
        ~>.coproduct.diassociate[ix.Type, iy.Type, iz.Type])(
        IsKind.either2(IsKind.either2(ix, iy), iz),
        IsKind.either2(ix, IsKind.either2(iy, iz))
      )
  }


}
