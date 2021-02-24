package io.cosmo.exo.internalstuff

import cats.implicits._
import io.cosmo.exo.categories.{Associative, Cartesian, Cocartesian, Distributive}
import io.cosmo.exo.{UnitK2, VoidK2, ~~>, ∀∀}

private[exo] trait FunctionK2Object {
  def id[F[_,_]]: F ~~> F = ∀∀.mk[F ~~> F].from(identity)
  def andThen[F[_,_], G[_,_], H[_,_]](fg: F ~~> G, gh: G ~~> H): F ~~> H = ∀∀.mk[F ~~> H].fromH(t => fg[t.A, t.B].andThen(gh[t.A, t.B]))
  def initiate[F[_,_]]: VoidK2 ~~> F = ∀∀.mk[VoidK2 ~~> F].from(identity)
  def terminate[F[_,_]]: F ~~> UnitK2 = ∀∀.mk[F ~~> UnitK2].from(_ => ())
  def distribute[F[_,_], G[_,_], H[_,_]]: λ[(a,b) => (F[a,b], Either[G[a,b], H[a,b]])] ~~> λ[(a,b) => Either[(F[a,b], G[a,b]), (F[a,b], H[a,b])]] =
    ∀∀.mk[λ[(a,b) => (F[a,b], Either[G[a,b], H[a,b]])] ~~> λ[(a,b) => Either[(F[a,b], G[a,b]), (F[a,b], H[a,b])]]].from(Distributive[* => *, Tuple2, Either].distribute)
  object product {
    def associate[F[_,_], G[_,_], H[_,_]]: λ[(a,b) => ((F[a,b], G[a,b]), H[a,b])] ~~> λ[(a,b) => (F[a,b], (G[a,b], H[a,b]))] =
      ∀∀.mk[λ[(a,b) => ((F[a,b], G[a,b]), H[a,b])] ~~> λ[(a,b) => (F[a,b], (G[a,b], H[a,b]))]].from(Associative[* => *, (*, *)].associate)
    def diassociate[F[_,_], G[_,_], H[_,_]]: λ[(a,b) => (F[a,b], (G[a,b], H[a,b]))] ~~> λ[(a,b) => ((F[a,b], G[a,b]), H[a,b])] =
      ∀∀.mk[λ[(a,b) => (F[a,b], (G[a,b], H[a,b]))] ~~> λ[(a,b) => ((F[a,b], G[a,b]), H[a,b])]].from(Associative[* => *, (*, *)].diassociate)
    def bimap[F[_,_], G[_,_], X[_,_], Y[_,_]](fg: F ~~> G, xy: X ~~> Y): λ[(a,b) => (F[a,b], X[a,b])] ~~> λ[(a,b) => (G[a,b], Y[a,b])] =
      ∀∀.mk[λ[(a,b) => (F[a,b], X[a,b])] ~~> λ[(a,b) => (G[a,b], Y[a,b])]].fromH(t => Associative[* => *, (*, *)].grouped(fg[t.A, t.B], xy[t.A, t.B]))
    def fst[F[_,_], G[_,_]]: λ[(a,b) => (F[a,b], G[a,b])] ~~> F = ∀∀.mk[λ[(a,b) => (F[a,b], G[a,b])] ~~> F].from(fg => fg._1)
    def snd[F[_,_], G[_,_]]: λ[(a,b) => (F[a,b], G[a,b])] ~~> G = ∀∀.mk[λ[(a,b) => (F[a,b], G[a,b])] ~~> G].from(fg => fg._2)
    def diag[F[_,_]]: F ~~> λ[(a,b) => (F[a,b], F[a,b])] = ∀∀.mk[F ~~> λ[(a,b) => (F[a,b], F[a,b])]].from(f => (f, f))
    def merge[F[_,_], G[_,_], H[_,_]](f: F ~~> G, g: F ~~> H): F ~~> λ[(a,b) => (G[a,b], H[a,b])] =
      ∀∀.mk[F ~~> λ[(a,b) => (G[a,b], H[a,b])]].fromH(t => Cartesian[* => *, (*, *)].&&&(f[t.A, t.B], g[t.A, t.B]))
    def idl  [F[_,_]]: λ[(a,b) => (UnitK2[a,b], F[a,b])] ~~> F = ∀∀.mk[λ[(a,b) => (UnitK2[a,b], F[a,b])] ~~> F].from(_._2)
    def coidl[F[_,_]]: F ~~> λ[(a,b) => (UnitK2[a,b], F[a,b])] = ∀∀.mk[F ~~> λ[(a,b) => (UnitK2[a,b], F[a,b])]].from(((), _))
    def idr  [F[_,_]]: λ[(a,b) => (F[a,b], UnitK2[a,b])] ~~> F = ∀∀.mk[λ[(a,b) => (F[a,b], UnitK2[a,b])] ~~> F].from(_._1)
    def coidr[F[_,_]]: F ~~> λ[(a,b) => (F[a,b], UnitK2[a,b])] = ∀∀.mk[F ~~> λ[(a,b) => (F[a,b], UnitK2[a,b])]].from((_, ()))
    def braid[F[_,_], G[_,_]]: λ[(a,b) => (F[a,b], G[a,b])] ~~> λ[(a,b) => (G[a,b], F[a,b])] =
      ∀∀.mk[λ[(a,b) => (F[a,b], G[a,b])] ~~> λ[(a,b) => (G[a,b], F[a,b])]].from(_.swap)
  }
  object coproduct {
    def diassociate[F[_,_], G[_,_], H[_,_]]: λ[(a,b) => Either[Either[F[a,b], G[a,b]], H[a,b]]] ~~> λ[(a,b) => Either[F[a,b], Either[G[a,b], H[a,b]]]] =
      ∀∀.mk[λ[(a,b) => Either[Either[F[a,b], G[a,b]], H[a,b]]] ~~> λ[(a,b) => Either[F[a,b], Either[G[a,b], H[a,b]]]]].from(Associative[* => *, Either].associate)
    def associate[F[_,_], G[_,_], H[_,_]]: λ[(a,b) => Either[F[a,b], Either[G[a,b], H[a,b]]]] ~~> λ[(a,b) => Either[Either[F[a,b], G[a,b]], H[a,b]]] =
      ∀∀.mk[λ[(a,b) => Either[F[a,b], Either[G[a,b], H[a,b]]]] ~~> λ[(a,b) => Either[Either[F[a,b], G[a,b]], H[a,b]]]].from(Associative[* => *, Either].diassociate)
    def bimap[F[_,_], G[_,_], X[_,_], Y[_,_]](fg: F ~~> G, xy: X ~~> Y): λ[(a,b) => Either[F[a,b], X[a,b]]] ~~> λ[(a,b) => Either[G[a,b], Y[a,b]]] =
      ∀∀.mk[λ[(a,b) => Either[F[a,b], X[a,b]]] ~~> λ[(a,b) => Either[G[a,b], Y[a,b]]]].fromH(t => Associative[* => *, Either].grouped(fg[t.A, t.B], xy[t.A, t.B]))
    def inl[F[_,_], G[_,_]]: F ~~> λ[(a,b) => Either[F[a,b], G[a,b]]] = ∀∀.mk[F ~~> λ[(a,b) => Either[F[a,b], G[a,b]]]].from(_.asLeft)
    def inr[F[_,_], G[_,_]]: G ~~> λ[(a,b) => Either[F[a,b], G[a,b]]] = ∀∀.mk[G ~~> λ[(a,b) => Either[F[a,b], G[a,b]]]].from(_.asRight)
    def codiag[F[_,_]]: λ[(a,b) => Either[F[a,b], F[a,b]]] ~~> F = ∀∀.mk[λ[(a,b) => Either[F[a,b], F[a,b]]] ~~> F].from(_.fold(identity, identity))
    def split[F[_,_], G[_,_], H[_,_]](f: F ~~> H, g: G ~~> H): λ[(a,b) => Either[F[a,b], G[a,b]]] ~~> H =
      ∀∀.mk[λ[(a,b) => Either[F[a,b], G[a,b]]] ~~> H].fromH(t => Cocartesian[* => *, Either].|||(f[t.A, t.B], g[t.A, t.B]))
    def idl[F[_,_]]: F ~~> λ[(a,b) => Either[VoidK2[a,b], F[a,b]]] = ∀∀.mk[F ~~> λ[(a,b) => Either[VoidK2[a,b], F[a,b]]]].from(_.asRight)
    def idr[F[_,_]]: F ~~> λ[(a,b) => Either[F[a,b], VoidK2[a,b]]] = ∀∀.mk[F ~~> λ[(a,b) => Either[F[a,b], VoidK2[a,b]]]].from(_.asLeft)
    def coidl  [F[_,_]]: λ[(a,b) => Either[VoidK2[a,b], F[a,b]]] ~~> F = ∀∀.mk[λ[(a,b) => Either[VoidK2[a,b], F[a,b]]] ~~> F].from(_.fold(identity, identity))
    def coidr  [F[_,_]]: λ[(a,b) => Either[F[a,b], VoidK2[a,b]]] ~~> F = ∀∀.mk[λ[(a,b) => Either[F[a,b], VoidK2[a,b]]] ~~> F].from(_.fold(identity, identity))
    def braid[F[_,_], G[_,_]]: λ[(a,b) => Either[F[a,b], G[a,b]]] ~~> λ[(a,b) => Either[G[a,b], F[a,b]]] =
      ∀∀.mk[λ[(a,b) => Either[F[a,b], G[a,b]]] ~~> λ[(a,b) => Either[G[a,b], F[a,b]]]].from(_.swap)
  }

}
