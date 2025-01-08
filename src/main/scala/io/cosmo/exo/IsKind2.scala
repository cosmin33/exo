package io.cosmo.exo

import io.cosmo.exo.internal.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

sealed trait IsKind2[A]:
  type Type[_,_]
  def pairInjectivity[P[_,_], X, Y](using ev: A === P[X, Y])(using i: IsInjective2[P]): (IsKind2[X], IsKind2[Y]) =
    throw UninitializedFieldError("IsKind2.pairInjectivity")

object IsKind2 extends IsKind2Implicits:
  type Aux[A, F[_,_]] = IsKind2[A] { type Type[X, Y] = F[X, Y] }
  def apply[A](using ev: IsKind2[A]): IsKind2[A] = ev

  def injectivity[A, B](a: IsKind2[A], b: IsKind2[B])(using eq: IsKind2[A] === IsKind2[B]): a.Type =~~= b.Type = Unsafe.isK2

  def isoInjectivity[A, B](using ia: IsKind2[A], ib: IsKind2[B]): (IsKind2[A] === IsKind2[B]) <=> (ia.Type =~~= ib.Type) =
    Iso.unsafe(_ => Unsafe.isK2, _ => Unsafe.is)

end IsKind2

trait IsKind2Implicits extends IsKind2Implicits01 {
  given impl[F[_,_]]: IsKind2.Aux[TypeK2[F], F] = new IsKind2[TypeK2[F]] { type Type[X, Y] = F[X, Y] }

  def pairInjectivity[F[_,_], A, B](using a: IsKind2[A], b: IsKind2[B])(using ii: IsInjective2[F])
  : IsKind2.Aux[F[A, B], [a,b] =>> F[a.Type[a,b], b.Type[a,b]]] = givenPairInj

  def injTuple[A, B](using l: IsKind2[A], r: IsKind2[B]): IsKind2.Aux[(A, B), [a, b] =>> (l.Type[a, b], r.Type[a, b])] =
    givenPairInj

  def injConjunction[A, B](using l: IsKind2[A], r: IsKind2[B]): IsKind2.Aux[A /\ B, [α, β] =>> l.Type[α, β] /\ r.Type[α, β]] =
    givenPairInj

  def injEither[A, B](using a: IsKind2[A], b: IsKind2[B]): IsKind2.Aux[Either[A, B], [α, β] =>> Either[a.Type[α, β], b.Type[α, β]]] =
    givenPairInj

  def injDisjunction[A, B](using a: IsKind2[A], b: IsKind2[B]): IsKind2.Aux[A \/ B, [α, β] =>> a.Type[α, β] \/ b.Type[α, β]] =
    \/.unsafeLeibniz.subst[[f[_,_]] =>> IsKind2.Aux[f[A, B], [o, p] =>> f[a.Type[o, p], b.Type[o, p]]]](injEither[A, B])

}

trait IsKind2Implicits01 extends IsKind2Implicits02 {
//  given arrowK[->[_,_], A, B](using a: IsKind2[A], b: IsKind2[B])
//  : IsKind2.Aux[ArrowK2[->, A, B], [a,b] =>> a.Type[a,b] -> b.Type[a,b]] =
//    new IsKind2[ArrowK2[->, A, B]]:
//      type Type[a, b] = a.Type[a,b] -> b.Type[a,b]
//      override def pairInjectivity[P[_,_], X, Y](using ev: ArrowK2[->, A, B] === P[X, Y])(using i: IsInjective2[P]): (IsKind2[X], IsKind2[Y]) =
//        val eq: P =~~= ArrowK2[->,*,*] = Unsafe.isK2
//        val (ax, by) = i.apply[A, B, X, Y](using eq.is[A, B] andThen ev)
//        (ax.subst(a), by.subst(b))
}

trait IsKind2Implicits02 {
  given givenPairInj[P[_,_], A, B, F[_,_], G[_,_]](using a: IsKind2.Aux[A, F], b: IsKind2.Aux[B, G])(using ii: IsInjective2[P])
  : IsKind2.Aux[P[A, B], [a,b] =>> P[F[a,b], G[a,b]]] =
    new IsKind2[P[A, B]]:
      type Type[a,b] = P[a.Type[a,b], b.Type[a,b]]
      override def pairInjectivity[Q[_,_], X, Y](using ev: P[A, B] === Q[X, Y])(using i: IsInjective2[Q]): (IsKind2[X], IsKind2[Y]) =
        val eq: Q =~~= P = Unsafe.isK2
        val (ax, by) = i.apply[A, B, X, Y](using eq.is[A, B] andThen ev)
        (ax.subst(a), by.subst(b))
}