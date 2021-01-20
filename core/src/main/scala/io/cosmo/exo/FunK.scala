package io.cosmo.exo

import io.cosmo.exo.categories.{Cartesian, Cocartesian, Distributive, Dual, DualModule, Endobifunctor, Initial, Opp, Subcat, Terminal}
import io.cosmo.exo.categories.functors.Endobifunctor
import io.cosmo.exo.evidence.{===, =~=, IsK}
import io.cosmo.exo.evidence.internal.Unsafe
import io.cosmo.exo.typeclasses.TypeF

sealed trait IsKind[A] {
  type Type[_]
}
object IsKind {
  type Aux[A, T[_]] = IsKind[A] { type Type[a] = T[a] }
  def apply[A](implicit a: IsKind[A]): IsKind.Aux[A, a.Type] = a

  implicit def impl[F[_]]: IsKind.Aux[TypeF[F], F] = new IsKind[TypeF[F]] { type Type[a] = F[a] }

  implicit def pair2[A, B](implicit l: IsKind[A], r: IsKind[B]): IsKind.Aux[(A, B), λ[α => (l.Type[α], r.Type[α])]] =
    new IsKind[(A, B)] { type Type[α] = (l.Type[α], r.Type[α]) }
  implicit def pair2_[A, B](implicit l: IsKind[A], r: IsKind[B]): IsKind.Aux[A /\ B, λ[α => l.Type[α] /\ r.Type[α]]] =
    new IsKind[A /\ B] { type Type[α] = l.Type[α] /\ r.Type[α] }

  implicit def either2[A, B](implicit a: IsKind[A], b: IsKind[B]): IsKind.Aux[Either[A, B], λ[α => Either[a.Type[α], b.Type[α]]]] =
    new IsKind[Either[A, B]] { type Type[α] = Either[a.Type[α], b.Type[α]] }
  implicit def either2_[A, B](implicit a: IsKind[A], b: IsKind[B]): IsKind.Aux[A \/ B, λ[α => \/[a.Type[α], b.Type[α]]]] =
    new IsKind[A \/ B] { type Type[α] = \/[a.Type[α], b.Type[α]] }

  def injectivity[A, B](ia: IsKind[A], ib: IsKind[B])(implicit eq: IsKind[A] === IsKind[B]): ia.Type =~= ib.Type =
    Unsafe.isK[ia.Type, ib.Type]
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
object FunK {
  type Aux[A, B, F[_], G[_]] = FunK[A, B] { type TypeA[a] = F[a]; type TypeB[a] = G[a] }
  def apply[F[_], G[_]](f: F ~> G): FunK.Aux[TypeF[F], TypeF[G], F, G] =
    new FunK[TypeF[F], TypeF[G]] {
      type TypeA[a] = F[a]
      type TypeB[a] = G[a]
      val kindA = IsKind[TypeF[F]]
      val kindB = IsKind[TypeF[G]]
      def fn = f
    }

  implicit def isoToFun[F[_], G[_]]: FunK[TypeF[F], TypeF[G]] <=> (F ~> G) = Iso.unsafe(_.unapply, apply)
  implicit def isoKIso[F[_], G[_]]: Iso[FunK, TypeF[F], TypeF[G]] <=> (F <~> G) =
    Iso.unsafe(ifk => <~>.unsafe(ifk.to.unapply, ifk.from.unapply), ifg => Iso.unsafe(apply(ifg.toK), apply(ifg.fromK)))

  import io.cosmo.exo.FunktionHelpers._

  implicit def subcat: Distributive.Aux[FunK, IsKind, (*, *), TypeF[UnitK], Either, TypeF[VoidK]]
    with Initial.Aux[FunK, IsKind, TypeF[VoidK]]
    with Terminal.Aux[FunK, IsKind, TypeF[UnitK]]
  = new FunkSubcat {}

  implicit def bifunctorTuple: Endobifunctor[FunK, Tuple2] = new FunkBifTuple {}

  implicit def bifunctorEither: Endobifunctor[FunK, Either] = new FunkBifEither {}

  implicit def cartesian: Cartesian.Aux[FunK, Tuple2, IsKind, TypeF[UnitK]] = new FunkCartesianTuple {}

  def cocartesianOpp: Cartesian.Aux[Opp[FunK]#l, Either, IsKind, TypeF[VoidK]] = new FunkCocartesianEither {}
  implicit def cocartesian: Cartesian.Aux[Dual[FunK,*,*], Either, IsKind, TypeF[VoidK]] =
    Dual.leibniz[FunK].subst[Cartesian.Aux[*[_,_], Either, IsKind, TypeF[VoidK]]](cocartesianOpp)

}

private[exo] object FunktionHelpers {
  trait FunkSubcat extends Distributive[FunK] with Initial[FunK]  with Terminal[FunK] {
    type TC[a] = IsKind[a]
    type ProductId = TypeF[UnitK]
    type ⨂[a,b] = (a, b)
    type SumId = TypeF[VoidK]
    type ⨁[a,b] = Either[a, b]
    type Initial = TypeF[VoidK]
    def initialTC = IsKind[TypeF[VoidK]]
    def initiate[A](implicit ia: IsKind[A]): FunK[TypeF[VoidK], A] =
      new FunK[TypeF[VoidK], A] {
        type TypeA[a] = VoidK[a]
        type TypeB[a] = ia.Type[a]
        def kindA: IsKind.Aux[TypeF[VoidK], VoidK] = implicitly
        def kindB: IsKind.Aux[A, ia.Type] = ia
        def fn: VoidK ~> ia.Type = ~>.initiate[ia.Type]
      }
    type Terminal = TypeF[UnitK]
    def terminalTC = IsKind[TypeF[UnitK]]
    def terminate[A](implicit ia: IsKind[A]): FunK[A, TypeF[UnitK]] =
      new FunK[A, TypeF[UnitK]] {
        type TypeA[a] = ia.Type[a]
        type TypeB[a] = UnitK[a]
        def kindA = ia
        def kindB = implicitly
        def fn: ia.Type ~> UnitK = ~>.terminate[ia.Type]
      }
    def cartesian = implicitly
    def cocartesian = implicitly
    def id[A](implicit ia: IsKind[A]): FunK[A, A] = new FunK[A, A] {
      type TypeA[a] = ia.Type[a]
      type TypeB[a] = ia.Type[a]
      def kindA = ia
      def kindB = ia
      def fn = ~>.id
    }
    def andThen[A, B, C](ab: FunK[A, B], bc: FunK[B, C]): FunK[A, C] = new FunK[A, C] {
      type TypeA[a] = ab.TypeA[a]
      type TypeB[a] = bc.TypeB[a]
      def kindA = ab.kindA
      def kindB = bc.kindB
      def fn = ~>.andThen(ab.fn, IsKind.injectivity(bc.kindA, ab.kindB).subst[λ[f[_] => f ~> bc.TypeB]](bc.fn))
    }
    def distribute[A, B, C](implicit ia: IsKind[A], ib: IsKind[B], ic: IsKind[C]): FunK[(A, Either[B, C]), Either[(A, B), (A, C)]] =
      new FunK[(A, Either[B, C]), Either[(A, B), (A, C)]] {
        type TypeA[a] = (ia.Type[a], Either[ib.Type[a], ic.Type[a]])
        type TypeB[a] = Either[(ia.Type[a], ib.Type[a]), (ia.Type[a], ic.Type[a])]
        def kindA = IsKind.pair2(ia, IsKind.either2(ib, ic))
        def kindB = IsKind.either2(IsKind.pair2(ia, ib), IsKind.pair2(ia, ic))
        def fn = ~>.distribute
      }
  }

  trait FunkBifTuple extends Endobifunctor[FunK, Tuple2] {
    def bimap[A, X, B, Y](left: FunK[A, X], right: FunK[B, Y]): FunK[(A, B), (X, Y)] =
      new FunK[(A, B), (X, Y)] {
        type TypeA[a] = (left.TypeA[a], right.TypeA[a])
        type TypeB[a] = (left.TypeB[a], right.TypeB[a])
        val kindA = IsKind.pair2(left.kindA, right.kindA)
        val kindB = IsKind.pair2(left.kindB, right.kindB)
        def fn: TypeA ~> TypeB = ~>.product.bimap(left.fn, right.fn)
      }
  }

  trait FunkBifEither extends Endobifunctor[FunK, Either] {
    def bimap[A, X, B, Y](left: FunK[A, X], right: FunK[B, Y]): FunK[Either[A, B], Either[X, Y]] =
      new FunK[Either[A, B], Either[X, Y]] {
        type TypeA[a] = Either[left.TypeA[a], right.TypeA[a]]
        type TypeB[a] = Either[left.TypeB[a], right.TypeB[a]]
        val kindA = IsKind.either2(left.kindA, right.kindA)
        val kindB = IsKind.either2(left.kindB, right.kindB)
        def fn: TypeA ~> TypeB = ~>.coproduct.bimap(left.fn, right.fn)
      }
  }

  trait FunkCartesianTuple extends Cartesian[FunK, Tuple2] {
    type Id = TypeF[UnitK]
    type TC[a] = IsKind[a]
    def C: Subcat.Aux[FunK, IsKind] = implicitly
    def bifunctor: Endobifunctor[FunK, Tuple2] = implicitly
    def fst[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), A] =
      new FunK[(A, B), A] {
        type TypeA[a] = (ia.Type[a], ib.Type[a])
        type TypeB[a] = ia.Type[a]
        def kindA = IsKind.pair2(ia, ib)
        def kindB = ia
        def fn: TypeA ~> ia.Type = ~>.product.fst
      }
    def snd[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), B] =
      new FunK[(A, B), B] {
        type TypeA[a] = (ia.Type[a], ib.Type[a])
        type TypeB[a] = ib.Type[a]
        def kindA = IsKind.pair2(ia, ib)
        def kindB = ib
        def fn = ~>.product.snd
      }
    def diag[A](implicit ia: IsKind[A]): FunK[A, (A, A)] = new FunK[A, (A, A)] {
      type TypeA[a] = ia.Type[a]
      type TypeB[a] = (ia.Type[a], ia.Type[a])
      def kindA = ia
      def kindB = IsKind.pair2(ia, ia)
      def fn = ~>.product.diag
    }
    def &&&[X, Y, Z](f: FunK[X, Y], g: FunK[X, Z]): FunK[X, (Y, Z)] =
      new FunK[X, (Y, Z)] {
        type TypeA[a] = f.TypeA[a]
        type TypeB[a] = (f.TypeB[a], g.TypeB[a])
        def kindA = f.kindA
        def kindB = IsKind.pair2(f.kindB, g.kindB)
        def fn = ~>.product.merge(f.fn, IsKind.injectivity(g.kindA, f.kindA).subst[λ[f[_] => f ~> g.TypeB]](g.fn))
      }
    def idl  [A](implicit ia: IsKind[A]): FunK[(TypeF[UnitK], A), A] =
      new FunK[(TypeF[UnitK], A), A] {
        type TypeA[a] = (UnitK[a], ia.Type[a])
        type TypeB[a] = ia.Type[a]
        def kindA = IsKind.pair2(IsKind[TypeF[UnitK]], ia)
        def kindB = ia
        def fn = ~>.product.idl
      }
    def coidl[A](implicit ia: IsKind[A]): FunK[A, (TypeF[UnitK], A)] =
      new FunK[A, (TypeF[UnitK], A)] {
        type TypeA[a] = ia.Type[a]
        type TypeB[a] = (UnitK[a], ia.Type[a])
        def kindA = ia
        def kindB = IsKind.pair2(IsKind[TypeF[UnitK]], ia)
        def fn = ~>.product.coidl
      }
    def idr  [A](implicit ia: IsKind[A]): FunK[(A, TypeF[UnitK]), A] =
      new FunK[(A, TypeF[UnitK]), A] {
        type TypeA[a] = (ia.Type[a], UnitK[a])
        type TypeB[a] = ia.Type[a]
        def kindA = IsKind.pair2(ia, IsKind[TypeF[UnitK]])
        def kindB = ia
        def fn = ~>.product.idr
      }
    def coidr[A](implicit ia: IsKind[A]): FunK[A, (A, TypeF[UnitK])] =
      new FunK[A, (A, TypeF[UnitK])] {
        type TypeA[a] = ia.Type[a]
        type TypeB[a] = (ia.Type[a], UnitK[a])
        def kindA = ia
        def kindB = IsKind.pair2(ia, IsKind[TypeF[UnitK]])
        def fn = ~>.product.coidr
      }
    def braid[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[(A, B), (B, A)] =
      new FunK[(A, B), (B, A)] {
        type TypeA[a] = (ia.Type[a], ib.Type[a])
        type TypeB[a] = (ib.Type[a], ia.Type[a])
        def kindA = IsKind.pair2(ia, ib)
        def kindB = IsKind.pair2(ib, ia)
        def fn = ~>.product.braid
      }
    def associate  [X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[((X, Y), Z), (X, (Y, Z))] =
      new FunK[((X, Y), Z), (X, (Y, Z))] {
        type TypeA[a] = ((ix.Type[a], iy.Type[a]), iz.Type[a])
        type TypeB[a] = (ix.Type[a], (iy.Type[a], iz.Type[a]))
        def kindA = IsKind.pair2(IsKind.pair2(ix, iy), iz)
        def kindB = IsKind.pair2(ix, IsKind.pair2(iy, iz))
        def fn = ~>.product.associate
      }
    def diassociate[X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[(X, (Y, Z)), ((X, Y), Z)] =
      new FunK[(X, (Y, Z)), ((X, Y), Z)] {
        type TypeA[a] = (ix.Type[a], (iy.Type[a], iz.Type[a]))
        type TypeB[a] = ((ix.Type[a], iy.Type[a]), iz.Type[a])
        def kindA = IsKind.pair2(ix, IsKind.pair2(iy, iz))
        def kindB = IsKind.pair2(IsKind.pair2(ix, iy), iz)
        def fn = ~>.product.diassociate
      }
  }

  trait FunkCocartesianEither extends Cartesian[Opp[FunK]#l, Either] {
    type Id = TypeF[VoidK]
    type TC[a] = IsKind[a]
    def bifunctor = DualModule.oppEndobifunctor(Endobifunctor[FunK, Either])
    def C = DualModule.oppSubcat(implicitly[Subcat.Aux[FunK, IsKind]])
    def fst[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[A, Either[A, B]] = new FunK[A, Either[A, B]] {
      type TypeA[a] = ia.Type[a]
      type TypeB[a] = Either[ia.Type[a], ib.Type[a]]
      def kindA = ia
      def kindB = IsKind.either2(ia, ib)
      def fn = ~>.coproduct.inl
    }
    def snd[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[B, Either[A, B]] = new FunK[B, Either[A, B]] {
      type TypeA[a] = ib.Type[a]
      type TypeB[a] = Either[ia.Type[a], ib.Type[a]]
      def kindA = ib
      def kindB = IsKind.either2(ia, ib)
      def fn = ~>.coproduct.inr
    }
    def diag[A](implicit ia: IsKind[A]): FunK[Either[A, A], A] = new FunK[Either[A, A], A] {
      type TypeA[a] = Either[ia.Type[a], ia.Type[a]]
      type TypeB[a] = ia.Type[a]
      def kindA = IsKind.either2(ia, ia)
      def kindB = ia
      def fn = ~>.coproduct.codiag
    }
    def &&&[X, Y, Z](f: FunK[Y, X], g: FunK[Z, X]): FunK[Either[Y, Z], X] =
      new FunK[Either[Y, Z], X] {
        type TypeA[a] = Either[f.TypeA[a], g.TypeA[a]]
        type TypeB[a] = f.TypeB[a]
        def kindA = IsKind.either2(f.kindA, g.kindA)
        def kindB = f.kindB
        def fn = ~>.coproduct.split(f.fn, IsKind.injectivity(g.kindB, f.kindB).subst[λ[f[_] => g.TypeA ~> f]](g.fn))
      }
    def idl  [A](implicit ia: IsKind[A]): FunK[A, Either[TypeF[VoidK], A]] =
      new FunK[A, Either[TypeF[VoidK], A]] {
        type TypeA[a] = ia.Type[a]
        type TypeB[a] = Either[VoidK[a], ia.Type[a]]
        def kindA = ia
        def kindB = IsKind.either2(IsKind[TypeF[VoidK]], ia)
        def fn = ~>.coproduct.idl
      }
    def coidl[A](implicit ia: IsKind[A]): FunK[Either[TypeF[VoidK], A], A] =
      new FunK[Either[TypeF[VoidK], A], A] {
        type TypeA[a] = Either[VoidK[a], ia.Type[a]]
        type TypeB[a] = ia.Type[a]
        def kindA = IsKind.either2(IsKind[TypeF[VoidK]], ia)
        def kindB = ia
        def fn = ~>.coproduct.coidl
      }
    def idr  [A](implicit ia: IsKind[A]): FunK[A, Either[A, TypeF[VoidK]]] =
      new FunK[A, Either[A, TypeF[VoidK]]] {
        type TypeA[a] = ia.Type[a]
        type TypeB[a] = Either[ia.Type[a], VoidK[a]]
        def kindA = ia
        def kindB = IsKind.either2(ia, IsKind[TypeF[VoidK]])
        def fn = ~>.coproduct.idr
      }
    def coidr[A](implicit ia: IsKind[A]): FunK[Either[A, TypeF[VoidK]], A] =
      new FunK[Either[A, TypeF[VoidK]], A] {
        type TypeA[a] = Either[ia.Type[a], VoidK[a]]
        type TypeB[a] = ia.Type[a]
        def kindA = IsKind.either2(ia, IsKind[TypeF[VoidK]])
        def kindB = ia
        def fn = ~>.coproduct.coidr
      }
    def braid[A, B](implicit ia: IsKind[A], ib: IsKind[B]): FunK[Either[B, A], Either[A, B]] =
      new FunK[Either[B, A], Either[A, B]] {
        type TypeA[a] = Either[ib.Type[a], ia.Type[a]]
        type TypeB[a] = Either[ia.Type[a], ib.Type[a]]
        def kindA = IsKind.either2(ib, ia)
        def kindB = IsKind.either2(ia, ib)
        def fn = ~>.coproduct.braid
      }
    def associate  [X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[X, Either[Y, Z]], Either[Either[X, Y], Z]] =
      new FunK[Either[X, Either[Y, Z]], Either[Either[X, Y], Z]] {
        type TypeA[a] = Either[ix.Type[a], Either[iy.Type[a], iz.Type[a]]]
        type TypeB[a] = Either[Either[ix.Type[a], iy.Type[a]], iz.Type[a]]
        def kindA = IsKind.either2(ix, IsKind.either2(iy, iz))
        def kindB = IsKind.either2(IsKind.either2(ix, iy), iz)
        def fn = ~>.coproduct.associate
      }
    def diassociate[X, Y, Z](implicit ix: IsKind[X], iy: IsKind[Y], iz: IsKind[Z]): FunK[Either[Either[X, Y], Z], Either[X, Either[Y, Z]]] =
      new FunK[Either[Either[X, Y], Z], Either[X, Either[Y, Z]]] {
        type TypeA[a] = Either[Either[ix.Type[a], iy.Type[a]], iz.Type[a]]
        type TypeB[a] = Either[ix.Type[a], Either[iy.Type[a], iz.Type[a]]]
        def kindA = IsKind.either2(IsKind.either2(ix, iy), iz)
        def kindB = IsKind.either2(ix, IsKind.either2(iy, iz))
        def fn = ~>.coproduct.diassociate
      }
  }


}
