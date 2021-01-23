package io.cosmo.exo.internalstuff

import cats.implicits._
import io.cosmo.exo.categories.{Associative, Cartesian, Cocartesian, Distributive}
import io.cosmo.exo.{UnitK, VoidK, ~>, ∀}

private[exo] trait FunctionKObject {
  def id[F[_]]: F ~> F = ∀.mk[F ~> F].from(identity)
  def andThen[F[_], G[_], H[_]](fg: F ~> G, gh: G ~> H): F ~> H = ∀.mk[F ~> H].fromH(t => fg[t.T].andThen(gh[t.T]))
  def initiate[F[_]]: VoidK ~> F = ∀.mk[VoidK ~> F].from(identity)
  def terminate[F[_]]: F ~> UnitK = ∀.mk[F ~> UnitK].from(_ => ())
  def distribute[F[_], G[_], H[_]]: λ[a => (F[a], Either[G[a], H[a]])] ~> λ[a => Either[(F[a], G[a]), (F[a], H[a])]] =
    ∀.mk[λ[a => (F[a], Either[G[a], H[a]])] ~> λ[a => Either[(F[a], G[a]), (F[a], H[a])]]].from(Distributive[* => *, Tuple2, Either].distribute)
  object product {
    def associate  [F[_], G[_], H[_]]: λ[a => ((F[a], G[a]), H[a])] ~> λ[a => (F[a], (G[a], H[a]))] =
      ∀.mk[λ[a => ((F[a], G[a]), H[a])] ~> λ[a => (F[a], (G[a], H[a]))]].from(Associative[* => *, (*, *)].associate)
    def diassociate[F[_], G[_], H[_]]: λ[a => (F[a], (G[a], H[a]))] ~> λ[a => ((F[a], G[a]), H[a])] =
      ∀.mk[λ[a => (F[a], (G[a], H[a]))] ~> λ[a => ((F[a], G[a]), H[a])]].from(Associative[* => *, (*, *)].diassociate)
    def bimap[F[_], G[_], X[_], Y[_]](fg: F ~> G, xy: X ~> Y): λ[a => (F[a], X[a])] ~> λ[a => (G[a], Y[a])] =
      ∀.mk[λ[a => (F[a], X[a])] ~> λ[a => (G[a], Y[a])]].fromH(t => Associative[* => *, (*, *)].grouped(fg[t.T], xy[t.T]))
    def fst[F[_], G[_]]: λ[a => (F[a], G[a])] ~> F = ∀.mk[λ[a => (F[a], G[a])] ~> F].from(fg => fg._1)
    def snd[F[_], G[_]]: λ[a => (F[a], G[a])] ~> G = ∀.mk[λ[a => (F[a], G[a])] ~> G].from(fg => fg._2)
    def diag[F[_]]: F ~> λ[a => (F[a], F[a])] = ∀.mk[F ~> λ[a => (F[a], F[a])]].from(f => (f, f))
    def merge[F[_], G[_], H[_]](f: F ~> G, g: F ~> H): F ~> λ[a => (G[a], H[a])] =
      ∀.mk[F ~> λ[a => (G[a], H[a])]].fromH(t => Cartesian[* => *, (*, *)].&&&(f[t.T], g[t.T]))
    def idl  [F[_]]: λ[a => (UnitK[a], F[a])] ~> F = ∀.mk[λ[a => (UnitK[a], F[a])] ~> F].from(_._2)
    def coidl[F[_]]: F ~> λ[a => (UnitK[a], F[a])] = ∀.mk[F ~> λ[a => (UnitK[a], F[a])]].from(((), _))
    def idr  [F[_]]: λ[a => (F[a], UnitK[a])] ~> F = ∀.mk[λ[a => (F[a], UnitK[a])] ~> F].from(_._1)
    def coidr[F[_]]: F ~> λ[a => (F[a], UnitK[a])] = ∀.mk[F ~> λ[a => (F[a], UnitK[a])]].from((_, ()))
    def braid[F[_], G[_]]: λ[a => (F[a], G[a])] ~> λ[a => (G[a], F[a])] =
      ∀.mk[λ[a => (F[a], G[a])] ~> λ[a => (G[a], F[a])]].from(_.swap)
  }
  object coproduct {
    def diassociate[F[_], G[_], H[_]]: λ[a => Either[Either[F[a], G[a]], H[a]]] ~> λ[a => Either[F[a], Either[G[a], H[a]]]] =
      ∀.mk[λ[a => Either[Either[F[a], G[a]], H[a]]] ~> λ[a => Either[F[a], Either[G[a], H[a]]]]].from(Associative[* => *, Either].associate)
    def associate[F[_], G[_], H[_]]: λ[a => Either[F[a], Either[G[a], H[a]]]] ~> λ[a => Either[Either[F[a], G[a]], H[a]]] =
      ∀.mk[λ[a => Either[F[a], Either[G[a], H[a]]]] ~> λ[a => Either[Either[F[a], G[a]], H[a]]]].from(Associative[* => *, Either].diassociate)
    def bimap[F[_], G[_], X[_], Y[_]](fg: F ~> G, xy: X ~> Y): λ[a => Either[F[a], X[a]]] ~> λ[a => Either[G[a], Y[a]]] =
      ∀.mk[λ[a => Either[F[a], X[a]]] ~> λ[a => Either[G[a], Y[a]]]].fromH(t => Associative[* => *, Either].grouped(fg[t.T], xy[t.T]))
    def inl[F[_], G[_]]: F ~> λ[a => Either[F[a], G[a]]] = ∀.mk[F ~> λ[a => Either[F[a], G[a]]]].from(_.asLeft)
    def inr[F[_], G[_]]: G ~> λ[a => Either[F[a], G[a]]] = ∀.mk[G ~> λ[a => Either[F[a], G[a]]]].from(_.asRight)
    def codiag[F[_]]: λ[a => Either[F[a], F[a]]] ~> F = ∀.mk[λ[a => Either[F[a], F[a]]] ~> F].from(_.fold(identity, identity))
    def split[F[_], G[_], H[_]](f: F ~> H, g: G ~> H): λ[a => Either[F[a], G[a]]] ~> H =
      ∀.mk[λ[a => Either[F[a], G[a]]] ~> H].fromH(t => Cocartesian[* => *, Either].|||(f[t.T], g[t.T]))
    def coidl  [F[_]]: λ[a => Either[VoidK[a], F[a]]] ~> F = ∀.mk[λ[a => Either[VoidK[a], F[a]]] ~> F].from(_.fold(identity, identity))
    def idl[F[_]]: F ~> λ[a => Either[VoidK[a], F[a]]] = ∀.mk[F ~> λ[a => Either[VoidK[a], F[a]]]].from(_.asRight)
    def coidr  [F[_]]: λ[a => Either[F[a], VoidK[a]]] ~> F = ∀.mk[λ[a => Either[F[a], VoidK[a]]] ~> F].from(_.fold(identity, identity))
    def idr[F[_]]: F ~> λ[a => Either[F[a], VoidK[a]]] = ∀.mk[F ~> λ[a => Either[F[a], VoidK[a]]]].from(_.asLeft)
    def braid[F[_], G[_]]: λ[a => Either[F[a], G[a]]] ~> λ[a => Either[G[a], F[a]]] =
      ∀.mk[λ[a => Either[F[a], G[a]]] ~> λ[a => Either[G[a], F[a]]]].from(_.swap)
  }
}
