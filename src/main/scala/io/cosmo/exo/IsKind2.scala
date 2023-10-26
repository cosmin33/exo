package io.cosmo.exo

import io.cosmo.exo.internal.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

sealed trait IsKind2[A]:
  type Type[_,_]
  def tuple[X, Y](using ev: A === (X, Y)): (IsKind2[X], IsKind2[Y]) = throw UninitializedFieldError("IsKind2.tuple")
  def funk[X, Y](using ev: A === FunK2[X, Y]): (IsKind2[X], IsKind2[Y]) = throw UninitializedFieldError("IsKind2.funk")
  def either[X, Y](using ev: A === Either[X, Y]): (IsKind2[X], IsKind2[Y]) = throw UninitializedFieldError("IsKind2.either")

object IsKind2:
  type Aux[A, F[_,_]] = IsKind2[A] { type Type[X, Y] = F[X, Y] }
  def apply[A](using ev: IsKind2[A]): IsKind2[A] = ev

  given impl[F[_,_]]: IsKind2.Aux[TypeK2[F], F] = new IsKind2[TypeK2[F]] { type Type[X, Y] = F[X, Y] }

  given givenTuple[A, B](using l: IsKind2[A], r: IsKind2[B]): IsKind2.Aux[(A, B), [a, b] =>> (l.Type[a, b], r.Type[a, b])] =
    new IsKind2[(A, B)]:
      type Type[α, β] = (l.Type[α, β], r.Type[α, β])
      override def tuple[X, Y](using ev: (A, B) === (X, Y)): (IsKind2[X], IsKind2[Y]) =
        IsInjective2[Tuple2].apply.bimapFn(_.subst(l), _.subst(r))

  given givenConjunction[A, B](using l: IsKind2[A], r: IsKind2[B]): IsKind2.Aux[A /\ B, [α, β] =>> l.Type[α, β] /\ r.Type[α, β]] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> IsKind2.Aux[f[A, B], [o, p] =>> f[l.Type[o, p], r.Type[o, p]]]](givenTuple[A, B])

  given givenFunction[A, B](using a: IsKind2[A], b: IsKind2[B]): IsKind2.Aux[FunK2[A, B], [o, p] =>> a.Type[o, p] => b.Type[o, p]] =
    new IsKind2[FunK2[A, B]]:
      type Type[o, p] = a.Type[o, p] => b.Type[o, p]
      override def funk[X, Y](using ev: FunK2[A, B] === FunK2[X, Y]): (IsKind2[X], IsKind2[Y]) =
        IsInjective2[FunK2].apply.bimapFn(_.subst(a), _.subst(b))

  given givenEither[A, B](using a: IsKind2[A], b: IsKind2[B]): IsKind2.Aux[Either[A, B], [α, β] =>> Either[a.Type[α, β], b.Type[α, β]]] =
    new IsKind2[Either[A, B]]:
      type Type[α, β] = Either[a.Type[α, β], b.Type[α, β]]
      override def either[X, Y](using ev: Either[A, B] === Either[X, Y]): (IsKind2[X], IsKind2[Y]) =
        IsInjective2[Either].apply.bimapFn(_.subst(a), _.subst(b))

  given givenDisjunction[A, B](using a: IsKind2[A], b: IsKind2[B]): IsKind2.Aux[A \/ B, [α, β] =>> a.Type[α, β] \/ b.Type[α, β]] =
    \/.unsafeLeibniz.subst[[f[_,_]] =>> IsKind2.Aux[f[A, B], [o, p] =>> f[a.Type[o, p], b.Type[o, p]]]](givenEither[A, B])

  def tupleKind[A, B](ab: IsKind2[(A, B)]): (IsKind2[A], IsKind2[B]) = ab.tuple[A, B]
  def functionKind[A, B](ab: IsKind2[FunK2[A, B]]): (IsKind2[A], IsKind2[B]) = ab.funk[A, B]
  def eitherKind[A, B](ab: IsKind2[Either[A, B]]): (IsKind2[A], IsKind2[B]) = ab.either[A, B]

  def injectivity[A, B](a: IsKind2[A], b: IsKind2[B])(using eq: IsKind2[A] === IsKind2[B]): a.Type =~~= b.Type = Unsafe.isK2

  def isoInjectivity[A, B](using ia: IsKind2[A], ib: IsKind2[B]): (IsKind2[A] === IsKind2[B]) <=> (ia.Type =~~= ib.Type) =
    Iso.unsafe(_ => Unsafe.isK2, _ => Unsafe.is)

end IsKind2
