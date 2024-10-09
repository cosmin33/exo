package io.cosmo.exo

import io.cosmo.exo.internal.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

sealed trait IsKind[A]:
  type Type[_]
  def tuple[X, Y](using ev: A === (X, Y)): (IsKind[X], IsKind[Y]) = throw UninitializedFieldError("IsKind.tuple")
  def funk[X, Y](using ev: A === FunK[X, Y]): (IsKind[X], IsKind[Y]) = throw UninitializedFieldError("IsKind.funk")
  def either[X, Y](using ev: A === Either[X, Y]): (IsKind[X], IsKind[Y]) = throw UninitializedFieldError("IsKind.either")

object IsKind extends IsKindImplicits:
  type Aux[A, T[_]] = IsKind[A] { type Type[a] = T[a] }
  def apply[A](using a: IsKind[A]): IsKind.Aux[A, a.Type] = a

  def injectivity[A, B](a: IsKind[A], b: IsKind[B])(using eq: IsKind[A] === IsKind[B]): a.Type =~= b.Type = Unsafe.isK

  def isoInjectivity[A, B](using ia: IsKind[A], ib: IsKind[B]): (IsKind[A] === IsKind[B]) <=> (ia.Type =~= ib.Type) =
    Iso.unsafe(_ => Unsafe.isK, _ => Unsafe.is)
  
end IsKind

trait IsKindImplicits extends IsKindImplicits01 {
  given impl[F[_]]: IsKind.Aux[TypeK[F], F] = new IsKind[TypeK[F]] { type Type[a] = F[a] }

  given givenTuple[A, B](using l: IsKind[A], r: IsKind[B]): IsKind.Aux[(A, B), [α] =>> (l.Type[α], r.Type[α])] =
    new IsKind[(A, B)]:
      type Type[α] = (l.Type[α], r.Type[α])
      override def tuple[X, Y](using ev: (A, B) === (X, Y)): (IsKind[X], IsKind[Y]) =
        IsInjective2[Tuple2].apply.bimapFn(_.subst(l), _.subst(r))

  given givenConjunction[A, B](using l: IsKind[A], r: IsKind[B]): IsKind.Aux[A /\ B, [α] =>> l.Type[α] /\ r.Type[α]] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> IsKind.Aux[f[A, B], [o] =>> f[l.Type[o], r.Type[o]]]](givenTuple[A, B])

  given givenFunction[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[FunK[A, B], [o] =>> a.Type[o] => b.Type[o]] =
    new IsKind[FunK[A, B]]:
      type Type[o] = a.Type[o] => b.Type[o]
      override def funk[X, Y](using ev: FunK[A, B] === FunK[X, Y]): (IsKind[X], IsKind[Y]) =
        IsInjective2[FunK].apply.bimapFn(_.subst(a), _.subst(b))

  given givenEither[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[Either[A, B], [α] =>> Either[a.Type[α], b.Type[α]]] =
    new IsKind[Either[A, B]]:
      type Type[α] = Either[a.Type[α], b.Type[α]]
      override def either[X, Y](using ev: Either[A, B] === Either[X, Y]): (IsKind[X], IsKind[Y]) =
        IsInjective2[Either].apply.bimapFn(_.subst(a), _.subst(b))

  given givenDisjunction[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[A \/ B, [α] =>> a.Type[α] \/ b.Type[α]] =
    \/.unsafeLeibniz.subst[[f[_,_]] =>> IsKind.Aux[f[A, B], [o] =>> f[a.Type[o], b.Type[o]]]](givenEither[A, B])
}

trait IsKindImplicits01 {
  given givenInjPair[F[_,_], A, B](using a: IsKind[A], b: IsKind[B])(using i: IsInjective2[F])
  : IsKind.Aux[F[A, B], [α] =>> F[a.Type[α], b.Type[α]]] =
    new IsKind[F[A, B]] { type Type[α] = F[a.Type[α], b.Type[α]] }
}