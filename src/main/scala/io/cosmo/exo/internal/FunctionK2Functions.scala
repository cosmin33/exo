package io.cosmo.exo.internal

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.functors._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._

trait FunctionK2Functions {
  def id[F[_,_]]: F ~~> F = ∀∀.mk[F ~~> F].from(identity)
  def andThen[F[_,_], G[_,_], H[_,_]](fg: F ~~> G, gh: G ~~> H): F ~~> H =
    ∀∀.mk[F ~~> H].fromH([A, B] => () => f => gh.apply(fg.apply(f)))
  def initiate[F[_,_]]: VoidK2 ~~> F = ∀∀.mk[VoidK2 ~~> F].from(_.absurd)
  def terminate[F[_,_]]: F ~~> UnitK2 = ∀∀.mk[F ~~> UnitK2].from(_ => ())
  def distribute[F[_,_], G[_,_], H[_,_]]: ([a,b] =>> (F[a,b], Either[G[a,b], H[a,b]])) ~~> ([a,b] =>> Either[(F[a,b], G[a,b]), (F[a,b], H[a,b])]) =
    ∀∀.mk[([a,b] =>> (F[a,b], Either[G[a,b], H[a,b]])) ~~> ([a,b] =>> Either[(F[a,b], G[a,b]), (F[a,b], H[a,b])])].from(Distributive[* => *, Tuple2, Either].distribute)
  object product {
    def associate[F[_,_], G[_,_], H[_,_]]: ([a,b] =>> ((F[a,b], G[a,b]), H[a,b])) ~~> ([a,b] =>> (F[a,b], (G[a,b], H[a,b]))) =
      ∀∀.mk[([a,b] =>> ((F[a,b], G[a,b]), H[a,b])) ~~> ([a,b] =>> (F[a,b], (G[a,b], H[a,b])))].from(Associative[* => *, Tuple2].associate)
    def diassociate[F[_,_], G[_,_], H[_,_]]: ([a,b] =>> (F[a,b], (G[a,b], H[a,b]))) ~~> ([a,b] =>> ((F[a,b], G[a,b]), H[a,b])) =
      ∀∀.mk[([a,b] =>> (F[a,b], (G[a,b], H[a,b]))) ~~> ([a,b] =>> ((F[a,b], G[a,b]), H[a,b]))].from(Associative[* => *, Tuple2].diassociate)
    def bimap[F[_,_], G[_,_], X[_,_], Y[_,_]](fg: F ~~> G, xy: X ~~> Y): ([a,b] =>> (F[a,b], X[a,b])) ~~> ([a,b] =>> (G[a,b], Y[a,b])) =
      ∀∀.mk[([a,b] =>> (F[a,b], X[a,b])) ~~> ([a,b] =>> (G[a,b], Y[a,b]))].fromH([A, B] => () => fxa => (fg.apply(fxa._1), xy.apply(fxa._2)))
    def fst[F[_,_], G[_,_]]: ([a,b] =>> (F[a,b], G[a,b])) ~~> F = ∀∀.mk[([a,b] =>> (F[a,b], G[a,b])) ~~> F].from(_._1)
    def snd[F[_,_], G[_,_]]: ([a,b] =>> (F[a,b], G[a,b])) ~~> G = ∀∀.mk[([a,b] =>> (F[a,b], G[a,b])) ~~> G].from(_._2)
    def diag[F[_,_]]: F ~~> ([a,b] =>> (F[a,b], F[a,b])) = ∀∀.mk[F ~~> ([a,b] =>> (F[a,b], F[a,b]))].from(f => (f, f))
    def merge[F[_,_], G[_,_], H[_,_]](fg: F ~~> G, fh: F ~~> H): F ~~> ([a,b] =>> (G[a,b], H[a,b])) =
      ∀∀.mk[F ~~> ([a,b] =>> (G[a,b], H[a,b]))].from(f => (fg.apply(f), fh.apply(f)))
    def idl[F[_,_]]: ([a,b] =>> (UnitK2[a,b], F[a,b])) ~~> F = ∀∀.mk[([a,b] =>> (UnitK2[a,b], F[a,b])) ~~> F].from(_._2)
    def idr[F[_,_]]: ([a,b] =>> (F[a,b], UnitK2[a,b])) ~~> F = ∀∀.mk[([a,b] =>> (F[a,b], UnitK2[a,b])) ~~> F].from(_._1)
    def coidl[F[_,_]]: F ~~> ([a,b] =>> (UnitK2[a,b], F[a,b])) = ∀∀.mk[F ~~> ([a,b] =>> (UnitK2[a,b], F[a,b]))].from(((), _))
    def coidr[F[_,_]]: F ~~> ([a,b] =>> (F[a,b], UnitK2[a,b])) = ∀∀.mk[F ~~> ([a,b] =>> (F[a,b], UnitK2[a,b]))].from((_, ()))
    def braid[F[_,_], G[_,_]]: ([a,b] =>> (F[a,b], G[a,b])) ~~> ([a,b] =>> (G[a,b], F[a,b])) =
      ∀∀.mk[([a,b] =>> (F[a,b], G[a,b])) ~~> ([a,b] =>> (G[a,b], F[a,b]))].fromH([A, B] => () => fg => (fg._2, fg._1))
    def curry[F[_,_], G[_,_], H[_,_]](fg: ([a,b] =>> (F[a,b], G[a,b])) ~~> H): ∀∀[[a,b] =>> F[a,b] => G[a,b] => H[a,b]] =
      ∀∀.of[[a,b] =>> F[a,b] => G[a,b] => H[a,b]].from(f => g => fg.apply((f, g)))
    def uncurry[F[_,_], G[_,_], H[_,_]](fgh: ∀∀[[a,b] =>> F[a,b] => G[a,b] => H[a,b]]): ∀∀[[a,b] =>> ((F[a,b], G[a,b])) => H[a,b]] =
      ∀∀.of[[a,b] =>> ((F[a,b], G[a,b])) => H[a,b]].from(fg => fgh.apply(fg._1).apply(fg._2))
  }
  object coproduct {
    def diassociate[F[_,_], G[_,_], H[_,_]]: ([a,b] =>> Either[Either[F[a,b], G[a,b]], H[a,b]]) ~~> ([a,b] =>> Either[F[a,b], Either[G[a,b], H[a,b]]]) =
      ∀∀.mk[([a,b] =>> Either[Either[F[a,b], G[a,b]], H[a,b]]) ~~> ([a,b] =>> Either[F[a,b], Either[G[a,b], H[a,b]]])].from(Associative[* => *, Either].associate)
    def associate[F[_,_], G[_,_], H[_,_]]: ([a,b] =>> Either[F[a,b], Either[G[a,b], H[a,b]]]) ~~> ([a,b] =>> Either[Either[F[a,b], G[a,b]], H[a,b]]) =
      ∀∀.mk[([a,b] =>> Either[F[a,b], Either[G[a,b], H[a,b]]]) ~~> ([a,b] =>> Either[Either[F[a,b], G[a,b]], H[a,b]])].from(Associative[* => *, Either].diassociate)
    def bimap[F[_,_], G[_,_], X[_,_], Y[_,_]](fg: F ~~> G, xy: X ~~> Y): ([a,b] =>> Either[F[a,b], X[a,b]]) ~~> ([a,b] =>> Either[G[a,b], Y[a,b]]) =
      ∀∀.mk[([a,b] =>> Either[F[a,b], X[a,b]]) ~~> ([a,b] =>> Either[G[a,b], Y[a,b]])].fromH([A, B] => () => Associative[* => *, Either].grouped(fg[A, B], xy[A, B]))
    def inl[F[_,_], G[_,_]]: F ~~> ([a,b] =>> Either[F[a,b], G[a,b]]) = ∀∀.mk[F ~~> ([a,b] =>> Either[F[a,b], G[a,b]])].from(Left(_))
    def inr[F[_,_], G[_,_]]: G ~~> ([a,b] =>> Either[F[a,b], G[a,b]]) = ∀∀.mk[G ~~> ([a,b] =>> Either[F[a,b], G[a,b]])].from(Right(_))
    def codiag[F[_,_]]: ([a,b] =>> Either[F[a,b], F[a,b]]) ~~> F = ∀∀.mk[([a,b] =>> Either[F[a,b], F[a,b]]) ~~> F].from(_.fold(identity, identity))
    def split[F[_,_], G[_,_], H[_,_]](fh: F ~~> H, gh: G ~~> H): ([a,b] =>> Either[F[a,b], G[a,b]]) ~~> H =
      ∀∀.mk[([a,b] =>> Either[F[a,b], G[a,b]]) ~~> H].from(_.fold(fh.apply, gh.apply))
    def coidl[F[_,_]]: ([a,b] =>> Either[VoidK2[a,b], F[a,b]]) ~~> F = ∀∀.mk[([a,b] =>> Either[VoidK2[a,b], F[a,b]]) ~~> F].from(_.fold(identity, identity))
    def coidr[F[_,_]]: ([a,b] =>> Either[F[a,b], VoidK2[a,b]]) ~~> F = ∀∀.mk[([a,b] =>> Either[F[a,b], VoidK2[a,b]]) ~~> F].from(_.fold(identity, identity))
    def idl[F[_,_]]: F ~~> ([a,b] =>> Either[VoidK2[a,b], F[a,b]]) = ∀∀.mk[F ~~> ([a,b] =>> Either[VoidK2[a,b], F[a,b]])].from(_.asRight)
    def idr[F[_,_]]: F ~~> ([a,b] =>> Either[F[a,b], VoidK2[a,b]]) = ∀∀.mk[F ~~> ([a,b] =>> Either[F[a,b], VoidK2[a,b]])].from(_.asLeft)
    def braid[F[_,_], G[_,_]]: ([a,b] =>> Either[F[a,b], G[a,b]]) ~~> ([a,b] =>> Either[G[a,b], F[a,b]]) =
      ∀∀.mk[([a,b] =>> Either[F[a,b], G[a,b]]) ~~> ([a,b] =>> Either[G[a,b], F[a,b]])].from(_.swap)
  }
}