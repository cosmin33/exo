package io.cosmo.exo

import io.cosmo.exo.internal.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

sealed trait IsHKind[A]:
  type Type[_[_]]
  def tuple[X, Y](using ev: A === (X, Y)): (IsHKind[X], IsHKind[Y]) = throw UninitializedFieldError("IsHKind.tuple")
  def function[X, Y](using ev: A === FunH[X, Y]): (IsHKind[X], IsHKind[Y]) = throw UninitializedFieldError("IsHKind.funk")
  def either[X, Y](using ev: A === Either[X, Y]): (IsHKind[X], IsHKind[Y]) = throw UninitializedFieldError("IsHKind.either")

object IsHKind:
  type Aux[A, T[_[_]]] = IsHKind[A] { type Type[f[_]] = T[f] }
  def apply[A](using a: IsHKind[A]): IsHKind.Aux[A, a.Type] = a

  given impl[F[_[_]]]: IsHKind.Aux[TypeHK[F], F] = new IsHKind[TypeHK[F]] { type Type[f[_]] = F[f] }

  given givenTuple[A, B](using l: IsHKind[A], r: IsHKind[B]): IsHKind.Aux[(A, B), [f[_]] =>> (l.Type[f], r.Type[f])] =
    new IsHKind[(A, B)]:
      type Type[f[_]] = (l.Type[f], r.Type[f])
      override def tuple[X, Y](using ev: (A, B) === (X, Y)): (IsHKind[X], IsHKind[Y]) =
        IsInjective2[Tuple2].apply.bimapFn(_.subst(l), _.subst(r))

  given givenConjunction[A, B](using l: IsHKind[A], r: IsHKind[B]): IsHKind.Aux[A /\ B, [f[_]] =>> l.Type[f] /\ r.Type[f]] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> IsHKind.Aux[f[A, B], [o[_]] =>> f[l.Type[o], r.Type[o]]]](givenTuple[A, B])

  given givenFunction[A, B](using a: IsHKind[A], b: IsHKind[B]): IsHKind.Aux[FunH[A, B], [o[_]] =>> a.Type[o] => b.Type[o]] =
    new IsHKind[FunH[A, B]]:
      type Type[o[_]] = a.Type[o] => b.Type[o]
      override def function[X, Y](using ev: FunH[A, B] === FunH[X, Y]): (IsHKind[X], IsHKind[Y]) =
        IsInjective2[FunH].apply.bimapFn(_.subst(a), _.subst(b))

  given givenEither[A, B](using a: IsHKind[A], b: IsHKind[B]): IsHKind.Aux[Either[A, B], [f[_]] =>> Either[a.Type[f], b.Type[f]]] =
    new IsHKind[Either[A, B]]:
      type Type[f[_]] = Either[a.Type[f], b.Type[f]]
      override def either[X, Y](using ev: Either[A, B] === Either[X, Y]): (IsHKind[X], IsHKind[Y]) =
        IsInjective2[Either].apply.bimapFn(_.subst(a), _.subst(b))

  given givenDisjunction[A, B](using a: IsHKind[A], b: IsHKind[B]): IsHKind.Aux[A \/ B, [f[_]] =>> a.Type[f] \/ b.Type[f]] =
    \/.unsafeLeibniz.subst[[f[_,_]] =>> IsHKind.Aux[f[A, B], [o[_]] =>> f[a.Type[o], b.Type[o]]]](givenEither[A, B])

  def injectivity[A, B](a: IsHKind[A], b: IsHKind[B])(using eq: IsHKind[A] === IsHKind[B]): a.Type =≈= b.Type = Unsafe.isHK

  def isoInjectivity[A, B](using ia: IsHKind[A], ib: IsHKind[B]): (IsHKind[A] === IsHKind[B]) <=> (ia.Type =≈= ib.Type) =
    Iso.unsafe(_ => Unsafe.isHK, _ => Unsafe.is)

end IsHKind
