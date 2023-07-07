package io.cosmo.exo.internal

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.functors._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._

trait FunctionHKFunctions {
  def id[F[_[_]]]: F ≈> F = ∀~.mk[F ≈> F].from(identity)
  def andThen[F[_[_]], G[_[_]], H[_[_]]](fg: F ≈> G, gh: G ≈> H): F ≈> H = ∀~.mk[F ≈> H].from(fg.apply andThen gh.apply)
  def initiate[F[_[_]]]: VoidHK ≈> F = ∀~.mk[VoidHK ≈> F].from(identity)
  def terminate[F[_[_]]]: F ≈> UnitHK = ∀~.mk[F ≈> UnitHK].from(_ => ())
  def distribute[F[_[_]], G[_[_]], H[_[_]]](fg: F ≈> G, fh: F ≈> H): F ≈> ([a[_]] =>> (G[a], H[a])) =
    ∀~.mk[F ≈> ([a[_]] =>> (G[a], H[a]))].from(fa => (fg.apply(fa), fh.apply(fa)))
  object product {
    def associate[F[_[_]], G[_[_]], H[_[_]]]: ([a[_]] =>> ((F[a], G[a]), H[a])) ≈> ([a[_]] =>> (F[a], (G[a], H[a]))) =
      ∀~.mk[([a[_]] =>> ((F[a], G[a]), H[a])) ≈> ([a[_]] =>> (F[a], (G[a], H[a])))].from(Associative[* => *, (*, *)].associate)
    def diassociate[F[_[_]], G[_[_]], H[_[_]]]: ([a[_]] =>> (F[a], (G[a], H[a]))) ≈> ([a[_]] =>> ((F[a], G[a]), H[a])) =
      ∀~.mk[([a[_]] =>> (F[a], (G[a], H[a]))) ≈> ([a[_]] =>> ((F[a], G[a]), H[a]))].from(Associative[* => *, (*, *)].diassociate)
    def bimap[F[_[_]], G[_[_]], X[_[_]], Y[_[_]]](fg: F ≈> G, xy: X ≈> Y): ([a[_]] =>> (F[a], X[a])) ≈> ([a[_]] =>> (G[a], Y[a])) =
      ∀~.mk[([a[_]] =>> (F[a], X[a])) ≈> ([a[_]] =>> (G[a], Y[a]))].fromH([T[_]] => () => Associative[* => *, (*, *)].grouped(fg[T], xy[T]))
    def fst[F[_[_]], G[_[_]]]: ([a[_]] =>> (F[a], G[a])) ≈> F = ∀~.mk[([a[_]] =>> (F[a], G[a])) ≈> F].from(_._1)
    def snd[F[_[_]], G[_[_]]]: ([a[_]] =>> (F[a], G[a])) ≈> G = ∀~.mk[([a[_]] =>> (F[a], G[a])) ≈> G].from(_._2)
    def diag[F[_[_]]]: F ≈> ([a[_]] =>> (F[a], F[a])) = ∀~.mk[F ≈> ([a[_]] =>> (F[a], F[a]))].from(fa => (fa, fa))
    def merge[F[_[_]], G[_[_]], H[_[_]]](f: F ≈> G, g: F ≈> H): F ≈> ([a[_]] =>> (G[a], H[a])) =
      ∀~.mk[F ≈> ([a[_]] =>> (G[a], H[a]))].from(fa => (f.apply(fa), g.apply(fa)))
    def idl[F[_[_]]]: ([a[_]] =>> (UnitHK[a], F[a])) ≈> F = ∀~.mk[([a[_]] =>> (UnitHK[a], F[a])) ≈> F].from(_._2)
    def idr[F[_[_]]]: ([a[_]] =>> (F[a], UnitHK[a])) ≈> F = ∀~.mk[([a[_]] =>> (F[a], UnitHK[a])) ≈> F].from(_._1)
    def coidl[F[_[_]]]: F ≈> ([a[_]] =>> (UnitHK[a], F[a])) = ∀~.mk[F ≈> ([a[_]] =>> (UnitHK[a], F[a]))].from(fa => ((), fa))
    def coidr[F[_[_]]]: F ≈> ([a[_]] =>> (F[a], UnitHK[a])) = ∀~.mk[F ≈> ([a[_]] =>> (F[a], UnitHK[a]))].from(fa => (fa, ()))
    def braid[F[_[_]], G[_[_]]]: ([a[_]] =>> (F[a], G[a])) ≈> ([a[_]] =>> (G[a], F[a])) =
      ∀~.mk[([a[_]] =>> (F[a], G[a])) ≈> ([a[_]] =>> (G[a], F[a]))].from(_.swap)
  }
  object coproduct {
    def diassociate[F[_[_]], G[_[_]], H[_[_]]]: ([a[_]] =>> Either[Either[F[a], G[a]], H[a]]) ≈> ([a[_]] =>> Either[F[a], Either[G[a], H[a]]]) =
      ∀~.mk[([a[_]] =>> Either[Either[F[a], G[a]], H[a]]) ≈> ([a[_]] =>> Either[F[a], Either[G[a], H[a]]])].from(Associative[* => *, Either].associate)
    def associate[F[_[_]], G[_[_]], H[_[_]]]: ([a[_]] =>> Either[F[a], Either[G[a], H[a]]]) ≈> ([a[_]] =>> Either[Either[F[a], G[a]], H[a]]) =
      ∀~.mk[([a[_]] =>> Either[F[a], Either[G[a], H[a]]]) ≈> ([a[_]] =>> Either[Either[F[a], G[a]], H[a]])].from(Associative[* => *, Either].diassociate)
    def bimap[F[_[_]], G[_[_]], X[_[_]], Y[_[_]]](fg: F ≈> G, xy: X ≈> Y): ([a[_]] =>> Either[F[a], X[a]]) ≈> ([a[_]] =>> Either[G[a], Y[a]]) =
      ∀~.mk[([a[_]] =>> Either[F[a], X[a]]) ≈> ([a[_]] =>> Either[G[a], Y[a]])].fromH([T[_]] => () => Associative[* => *, Either].grouped(fg[T], xy[T]))
    def inl[F[_[_]], G[_[_]]]: F ≈> ([a[_]] =>> Either[F[a], G[a]]) = ∀~.mk[F ≈> ([a[_]] =>> Either[F[a], G[a]])].from(_.asLeft)
    def inr[F[_[_]], G[_[_]]]: G ≈> ([a[_]] =>> Either[F[a], G[a]]) = ∀~.mk[G ≈> ([a[_]] =>> Either[F[a], G[a]])].from(_.asRight)
    def codiag[F[_[_]]]: ([a[_]] =>> Either[F[a], F[a]]) ≈> F = ∀~.mk[([a[_]] =>> Either[F[a], F[a]]) ≈> F].from(_.fold(identity, identity))
    def split[F[_[_]], G[_[_]], H[_[_]]](f: F ≈> H, g: G ≈> H): ([a[_]] =>> Either[F[a], G[a]]) ≈> H =
      ∀~.mk[([a[_]] =>> Either[F[a], G[a]]) ≈> H].from(_.fold(f.apply, g.apply))
    def coidl[F[_[_]], G[_[_]]]: ([a[_]] =>> Either[VoidHK[a], F[a]]) ≈> F = ∀~.mk[([a[_]] =>> Either[VoidHK[a], F[a]]) ≈> F].from(_.fold(identity, identity))
    def coidr[F[_[_]], G[_[_]]]: ([a[_]] =>> Either[F[a], VoidHK[a]]) ≈> F = ∀~.mk[([a[_]] =>> Either[F[a], VoidHK[a]]) ≈> F].from(_.fold(identity, identity))
    def idl[F[_[_]]]: F ≈> ([a[_]] =>> Either[VoidHK[a], F[a]]) = ∀~.mk[F ≈> ([a[_]] =>> Either[VoidHK[a], F[a]])].from(_.asRight)
    def idr[F[_[_]]]: F ≈> ([a[_]] =>> Either[F[a], VoidHK[a]]) = ∀~.mk[F ≈> ([a[_]] =>> Either[F[a], VoidHK[a]])].from(_.asLeft)
    def braid[F[_[_]], G[_[_]]]: ([a[_]] =>> Either[F[a], G[a]]) ≈> ([a[_]] =>> Either[G[a], F[a]]) =
      ∀~.mk[([a[_]] =>> Either[F[a], G[a]]) ≈> ([a[_]] =>> Either[G[a], F[a]])].from(_.swap)
  }
}
