package io.cosmo.exo

import io.cosmo.exo.internal.*
import io.cosmo.exo.evidence.*

sealed trait IsKind[A] {
  type Type[_]
  def tuple[X, Y](using ev: A === (X, Y)): (IsKind[X], IsKind[Y]) = throw UninitializedFieldError("IsKind.tuple")
  def funk[X, Y](using ev: A === FunK[X, Y]): (IsKind[X], IsKind[Y]) = throw UninitializedFieldError("IsKind.funk")
}
object IsKind {
  type Aux[A, T[_]] = IsKind[A] { type Type[a] = T[a] }
  def apply[A](using a: IsKind[A]): IsKind.Aux[A, a.Type] = a

  given impl[F[_]]: IsKind.Aux[TypeK[F], F] = new IsKind[TypeK[F]] { type Type[a] = F[a] }

  given pair2[A, B](using l: IsKind[A], r: IsKind[B]): IsKind.Aux[(A, B), λ[α => (l.Type[α], r.Type[α])]] =
    new IsKind[(A, B)] {
      type Type[α] = (l.Type[α], r.Type[α])

      override def tuple[X, Y](using ev: (A, B) === (X, Y)): (IsKind[X], IsKind[Y]) = {
        val (eqAX, eqBY) = IsInjective2[Tuple2].apply
        eqAX.subst[IsKind](l) -> eqBY.subst[IsKind](r)
      }
    }
  given pair2_[A, B](using l: IsKind[A], r: IsKind[B]): IsKind.Aux[A /\ B, λ[α => l.Type[α] /\ r.Type[α]]] =
    /\.unsafeLeibniz.subst[[f[_,_]] =>> IsKind.Aux[f[A, B], [o] =>> f[l.Type[o], r.Type[o]]]](pair2[A, B])

  def unpair[A, B](ab: IsKind[(A, B)]): (IsKind[A], IsKind[B]) = ab.tuple[A, B]

  given function[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[FunK[A, B], [o] =>> a.Type[o] => b.Type[o]] =
    new IsKind[FunK[A, B]] { type Type[o] = a.Type[o] => b.Type[o] }
  given unFunction[A, B](using f: IsKind[FunK[A, B]]): (IsKind[A], IsKind[B]) = f.funk[A, B]

  given either2[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[Either[A, B], λ[α => Either[a.Type[α], b.Type[α]]]] =
    new IsKind[Either[A, B]] { type Type[α] = Either[a.Type[α], b.Type[α]] }
  given either2_[A, B](using a: IsKind[A], b: IsKind[B]): IsKind.Aux[A \/ B, λ[α => \/[a.Type[α], b.Type[α]]]] =
    new IsKind[A \/ B] { type Type[α] = \/[a.Type[α], b.Type[α]] }

  def injectivity[A, B](a: IsKind[A], b: IsKind[B])(using eq: IsKind[A] === IsKind[B]): a.Type =~= b.Type = Unsafe.isK

  def isoInjectivity[A, B](using ia: IsKind[A], ib: IsKind[B]): (IsKind[A] === IsKind[B]) <=> (ia.Type =~= ib.Type) =
    Iso.unsafe(_ => Unsafe.isK, _=> Unsafe.is)

}

sealed trait IsKind1[A] {
  type Type[_]
}

final case class KindOne[F[_]](dummy: Unit) extends IsKind1[TypeK[F]] {
  type Type[a] = F[a]
}

final case class KindProduct[F[_], G[_]](dummy: Unit) extends IsKind1[TypeK[[a] =>> (F[a], G[a])]] {
  type Type[a] = (F[a], G[a])
  def unpair: (IsKind1[TypeK[F]], IsKind1[TypeK[G]]) = (KindOne[F](()), KindOne[G](()))
}

final case class KindCoproduct[F[_], G[_]](dummy: Unit) extends IsKind1[TypeK[[a] =>> Either[F[a], G[a]]]] {
  type Type[a] = Either[F[a], G[a]]
  def unpair: (IsKind1[TypeK[F]], IsKind1[TypeK[G]]) = (KindOne[F](()), KindOne[G](()))
}

final case class KindFunction[F[_], G[_]](dummy: Unit) extends IsKind1[TypeK[[a] =>> F[a] => G[a]]] {
  type Type[a] = F[a] => G[a]
  def unpair: (IsKind1[TypeK[F]], IsKind1[TypeK[G]]) = (KindOne[F](()), KindOne[G](()))
}

object IsKind1 {
  type Aux[A, T[_]] = IsKind1[A] { type Type[a] = T[a] }
  def injectivity[A, B](a: IsKind1[A], b: IsKind1[B])(using eq: IsKind1[A] === IsKind1[B]): a.Type =~= b.Type = Unsafe.isK
}
