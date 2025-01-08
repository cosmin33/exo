package io.cosmo.exo

import io.cosmo.exo.internal.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

sealed trait IsHKind[A]:
  type Type[_[_]]
  def pairInjectivity[P[_,_], X, Y](using ev: A === P[X, Y])(using i: IsInjective2[P]): (IsHKind[X], IsHKind[Y]) =
    throw UninitializedFieldError("IsHKind.pairInjectivity")

object IsHKind extends IsHKindImplicits:
  type Aux[A, T[_[_]]] = IsHKind[A] { type Type[f[_]] = T[f] }
  def apply[A](using a: IsHKind[A]): IsHKind.Aux[A, a.Type] = a

  def injectivity[A, B](a: IsHKind[A], b: IsHKind[B])(using eq: IsHKind[A] === IsHKind[B]): a.Type =≈= b.Type = Unsafe.isHK

  def isoInjectivity[A, B](using ia: IsHKind[A], ib: IsHKind[B]): (IsHKind[A] === IsHKind[B]) <=> (ia.Type =≈= ib.Type) =
    Iso.unsafe(_ => Unsafe.isHK, _ => Unsafe.is)

end IsHKind

trait IsHKindImplicits extends IsHKindImplicits01 {
  given impl[F[_[_]]]: IsHKind.Aux[TypeHK[F], F] = new IsHKind[TypeHK[F]] { type Type[f[_]] = F[f] }

  def pairInjectivity[F[_,_], A, B](using a: IsHKind[A], b: IsHKind[B])(using ii: IsInjective2[F])
  : IsHKind.Aux[F[A, B], [α[_]] =>> F[a.Type[α], b.Type[α]]] = givenPairInj

  def injTuple[A, B](using l: IsHKind[A], r: IsHKind[B]): IsHKind.Aux[(A, B), [f[_]] =>> (l.Type[f], r.Type[f])] =
    givenPairInj

  def injConjunction[A, B](using l: IsHKind[A], r: IsHKind[B]): IsHKind.Aux[A /\ B, [f[_]] =>> l.Type[f] /\ r.Type[f]] =
    givenPairInj

  def injEither[A, B](using a: IsHKind[A], b: IsHKind[B]): IsHKind.Aux[Either[A, B], [f[_]] =>> Either[a.Type[f], b.Type[f]]] =
    givenPairInj

  def injDisjunction[A, B](using a: IsHKind[A], b: IsHKind[B]): IsHKind.Aux[A \/ B, [f[_]] =>> a.Type[f] \/ b.Type[f]] =
    givenPairInj

}

trait IsHKindImplicits01 extends IsHKindImplicits02 {
//  given arrowK[->[_,_], A, B](using a: IsHKind[A], b: IsHKind[B])
//  : IsHKind.Aux[ArrowH[->, A, B], [α[_]] =>> a.Type[α] -> b.Type[α]] =
//    new IsHKind[ArrowH[->, A, B]]:
//      type Type[α[_]] = a.Type[α] -> b.Type[α]
//      override def pairInjectivity[P[_,_], X, Y](using ev: ArrowH[->, A, B] === P[X, Y])(using i: IsInjective2[P]): (IsHKind[X], IsHKind[Y]) =
//        val eq: P =~~= ArrowH[->,*,*] = Unsafe.isK2
//        val (ax, by) = i.apply[A, B, X, Y](using eq.is[A, B] andThen ev)
//        (ax.subst(a), by.subst(b))
}

trait IsHKindImplicits02 {
  given givenPairInj[P[_,_], A, B, F[_[_]], G[_[_]]](using a: IsHKind.Aux[A, F], b: IsHKind.Aux[B, G])(using ii: IsInjective2[P])
  : IsHKind.Aux[P[A, B], [α[_]] =>> P[F[α], G[α]]] =
    new IsHKind[P[A, B]]:
      type Type[α[_]] = P[a.Type[α], b.Type[α]]
      override def pairInjectivity[Q[_,_], X, Y](using ev: P[A, B] === Q[X, Y])(using i: IsInjective2[Q]): (IsHKind[X], IsHKind[Y]) =
        val eq: Q =~~= P = Unsafe.isK2
        val (ax, by) = i.apply[A, B, X, Y](using eq.is[A, B] andThen ev)
        (ax.subst(a), by.subst(b))
}
