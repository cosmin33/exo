package io.cosmo.exo

import io.cosmo.exo.internal.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

sealed trait IsKind[A]:
  type Type[_]
  def pairInjectivity[P[_,_], X, Y](using ev: A === P[X, Y])(using i: IsInjective2[P]): (IsKind[X], IsKind[Y]) =
    throw UninitializedFieldError("IsKind.pairInjectivity")

object IsKind extends IsKindImplicits:
  type Aux[A, T[_]] = IsKind[A] { type Type[a] = T[a] }
  def apply[A](using a: IsKind[A]): IsKind.Aux[A, a.Type] = a

  def injectivity[A, B](a: IsKind[A], b: IsKind[B])(using eq: IsKind[A] === IsKind[B]): a.Type =~= b.Type = Unsafe.isK

  def isoInjectivity[A, B](using ia: IsKind[A], ib: IsKind[B]): (IsKind[A] === IsKind[B]) <=> (ia.Type =~= ib.Type) =
    Iso.unsafe(_ => Unsafe.isK, _ => Unsafe.is)
  
end IsKind

trait IsKindImplicits extends IsKindImplicits01 {
  given impl[F[_]]: IsKind.Aux[TypeK[F], F] = new IsKind[TypeK[F]] { type Type[a] = F[a] }

  def pairInjectivity[F[_,_], A, B](using a: IsKind[A], b: IsKind[B])(using ii: IsInjective2[F])
  : IsKind.Aux[F[A, B], [α] =>> F[a.Type[α], b.Type[α]]] = givenPairInj

  def injTuple[A, B](using l: IsKind[A], r: IsKind[B]): IsKind.Aux[(A, B), [α] =>> (l.Type[α], r.Type[α])] =
    givenPairInj

  def injConjunction[A, B](using l: IsKind[A], r: IsKind[B]): IsKind.Aux[A /\ B, [α] =>> l.Type[α] /\ r.Type[α]] =
    givenPairInj

  def injEither[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[Either[A, B], [α] =>> Either[a.Type[α], b.Type[α]]] =
    givenPairInj

  def injDisjunction[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[A \/ B, [α] =>> a.Type[α] \/ b.Type[α]] =
    givenPairInj

  // TODO: remove this (after refactor FunctionK to be an alias of ArrowK)
  def injFunction[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[FunK[A, B], [o] =>> a.Type[o] => b.Type[o]] =
    ???
}

trait IsKindImplicits01 extends IsKindImplicits02 {
  given arrowK[->[_,_], A, B](using a: IsKind[A], b: IsKind[B])
  : IsKind.Aux[ArrowK[->, A, B], [α] =>> a.Type[α] -> b.Type[α]] =
    new IsKind[ArrowK[->, A, B]]:
      type Type[α] = a.Type[α] -> b.Type[α]
      override def pairInjectivity[P[_,_], X, Y](using ev: ArrowK[->, A, B] === P[X, Y])(using i: IsInjective2[P]): (IsKind[X], IsKind[Y]) =
        val eq: P =~~= ArrowK[->,*,*] = Unsafe.isK2
        val (ax, by) = i.apply[A, B, X, Y](using eq.is[A, B] andThen ev)
        (ax.subst(a), by.subst(b))
}

trait IsKindImplicits02 {
  given givenPairInj[P[_,_], A, B, F[_], G[_]](using a: IsKind.Aux[A, F], b: IsKind.Aux[B, G])(using ii: IsInjective2[P])
  : IsKind.Aux[P[A, B], [α] =>> P[F[α], G[α]]] =
    new IsKind[P[A, B]]:
      type Type[α] = P[a.Type[α], b.Type[α]]
      override def pairInjectivity[Q[_,_], X, Y](using ev: P[A, B] === Q[X, Y])(using i: IsInjective2[Q]): (IsKind[X], IsKind[Y]) =
        val eq: Q =~~= P = Unsafe.isK2
        val (ax, by) = i.apply[A, B, X, Y](using eq.is[A, B] andThen ev)
        (ax.subst(a), by.subst(b))
}
