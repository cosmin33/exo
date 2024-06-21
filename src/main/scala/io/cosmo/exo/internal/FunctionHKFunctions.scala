package io.cosmo.exo.internal

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.functors._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._

trait FunctionHKFunctions {
  def id[A[_[_]]]: A ≈> A = ∀~.mk[A ≈> A].from(identity)
  def andThen[A[_[_]], B[_[_]], H[_[_]]](fg: A ≈> B, gh: B ≈> H): A ≈> H = ∀~.mk[A ≈> H].from(fg.apply andThen gh.apply)
  def initiate[A[_[_]]]: VoidHK ≈> A = ∀~.mk[VoidHK ≈> A].from(identity)
  def terminate[A[_[_]]]: A ≈> UnitHK = ∀~.mk[A ≈> UnitHK].from(_ => ())
  def distribute[A[_[_]], B[_[_]], C[_[_]]]: ([f[_]] =>> (A[f], Either[B[f], C[f]])) ≈> ([f[_]] =>> Either[(A[f], B[f]), (A[f], C[f])]) =
    ∀~.mk[([f[_]] =>> (A[f], Either[B[f], C[f]])) ≈> ([f[_]] =>> Either[(A[f], B[f]), (A[f], C[f])])].from(Distributive[* => *, Tuple2, Either].distribute)
  object product {
    def associate[A[_[_]], B[_[_]], H[_[_]]]: ([f[_]] =>> ((A[f], B[f]), H[f])) ≈> ([f[_]] =>> (A[f], (B[f], H[f]))) =
      ∀~.mk[([f[_]] =>> ((A[f], B[f]), H[f])) ≈> ([f[_]] =>> (A[f], (B[f], H[f])))].from(Associative[* => *, (*, *)].associate)
    def diassociate[A[_[_]], B[_[_]], H[_[_]]]: ([f[_]] =>> (A[f], (B[f], H[f]))) ≈> ([f[_]] =>> ((A[f], B[f]), H[f])) =
      ∀~.mk[([f[_]] =>> (A[f], (B[f], H[f]))) ≈> ([f[_]] =>> ((A[f], B[f]), H[f]))].from(Associative[* => *, (*, *)].diassociate)
    def bimap[A[_[_]], B[_[_]], X[_[_]], Y[_[_]]](ab: A ≈> B, xy: X ≈> Y): ([f[_]] =>> (A[f], X[f])) ≈> ([f[_]] =>> (B[f], Y[f])) =
      ∀~.mk[([f[_]] =>> (A[f], X[f])) ≈> ([f[_]] =>> (B[f], Y[f]))].fromH([T[_]] => () => Associative[* => *, (*, *)].grouped(ab[T], xy[T]))
    def fst[A[_[_]], B[_[_]]]: ([f[_]] =>> (A[f], B[f])) ≈> A = ∀~.mk[([f[_]] =>> (A[f], B[f])) ≈> A].from(_._1)
    def snd[A[_[_]], B[_[_]]]: ([f[_]] =>> (A[f], B[f])) ≈> B = ∀~.mk[([f[_]] =>> (A[f], B[f])) ≈> B].from(_._2)
    def diag[A[_[_]]]: A ≈> ([f[_]] =>> (A[f], A[f])) = ∀~.mk[A ≈> ([f[_]] =>> (A[f], A[f]))].from(fa => (fa, fa))
    def merge[A[_[_]], B[_[_]], H[_[_]]](f: A ≈> B, g: A ≈> H): A ≈> ([f[_]] =>> (B[f], H[f])) =
      ∀~.mk[A ≈> ([f[_]] =>> (B[f], H[f]))].from(fa => (f.apply(fa), g.apply(fa)))
    def idl[A[_[_]]]: ([f[_]] =>> (UnitHK[f], A[f])) ≈> A = ∀~.mk[([f[_]] =>> (UnitHK[f], A[f])) ≈> A].from(_._2)
    def idr[A[_[_]]]: ([f[_]] =>> (A[f], UnitHK[f])) ≈> A = ∀~.mk[([f[_]] =>> (A[f], UnitHK[f])) ≈> A].from(_._1)
    def coidl[A[_[_]]]: A ≈> ([f[_]] =>> (UnitHK[f], A[f])) = ∀~.mk[A ≈> ([f[_]] =>> (UnitHK[f], A[f]))].from(fa => ((), fa))
    def coidr[A[_[_]]]: A ≈> ([f[_]] =>> (A[f], UnitHK[f])) = ∀~.mk[A ≈> ([f[_]] =>> (A[f], UnitHK[f]))].from(fa => (fa, ()))
    def braid[A[_[_]], B[_[_]]]: ([f[_]] =>> (A[f], B[f])) ≈> ([f[_]] =>> (B[f], A[f])) =
      ∀~.mk[([f[_]] =>> (A[f], B[f])) ≈> ([f[_]] =>> (B[f], A[f]))].from(_.swap)
    def curry[A[_[_]], B[_[_]], C[_[_]]](f: ∀~[[f[_]] =>> (A[f], B[f]) => C[f]]): ∀~[[f[_]] =>> A[f] => B[f] => C[f]] =
      ∀~.of[[f[_]] =>> A[f] => B[f] => C[f]].from(a => b => f.apply(a, b))
    def uncurry[A[_[_]], B[_[_]], C[_[_]]](f: ∀~[[f[_]] =>> A[f] => B[f] => C[f]]): ∀~[[f[_]] =>> ((A[f], B[f])) => C[f]] =
      ∀~.of[[f[_]] =>> ((A[f], B[f])) => C[f]].from(ab => f.apply(ab._1).apply(ab._2))
  }
  object coproduct {
    def diassociate[A[_[_]], B[_[_]], H[_[_]]]: ([f[_]] =>> Either[Either[A[f], B[f]], H[f]]) ≈> ([f[_]] =>> Either[A[f], Either[B[f], H[f]]]) =
      ∀~.mk[([f[_]] =>> Either[Either[A[f], B[f]], H[f]]) ≈> ([f[_]] =>> Either[A[f], Either[B[f], H[f]]])].from(Associative[* => *, Either].associate)
    def associate[A[_[_]], B[_[_]], H[_[_]]]: ([f[_]] =>> Either[A[f], Either[B[f], H[f]]]) ≈> ([f[_]] =>> Either[Either[A[f], B[f]], H[f]]) =
      ∀~.mk[([f[_]] =>> Either[A[f], Either[B[f], H[f]]]) ≈> ([f[_]] =>> Either[Either[A[f], B[f]], H[f]])].from(Associative[* => *, Either].diassociate)
    def bimap[A[_[_]], B[_[_]], X[_[_]], Y[_[_]]](ab: A ≈> B, xy: X ≈> Y): ([f[_]] =>> Either[A[f], X[f]]) ≈> ([f[_]] =>> Either[B[f], Y[f]]) =
      ∀~.mk[([f[_]] =>> Either[A[f], X[f]]) ≈> ([f[_]] =>> Either[B[f], Y[f]])].fromH([T[_]] => () => Associative[* => *, Either].grouped(ab[T], xy[T]))
    def inl[A[_[_]], B[_[_]]]: A ≈> ([f[_]] =>> Either[A[f], B[f]]) = ∀~.mk[A ≈> ([f[_]] =>> Either[A[f], B[f]])].from(_.asLeft)
    def inr[A[_[_]], B[_[_]]]: B ≈> ([f[_]] =>> Either[A[f], B[f]]) = ∀~.mk[B ≈> ([f[_]] =>> Either[A[f], B[f]])].from(_.asRight)
    def codiag[A[_[_]]]: ([f[_]] =>> Either[A[f], A[f]]) ≈> A = ∀~.mk[([f[_]] =>> Either[A[f], A[f]]) ≈> A].from(_.fold(identity, identity))
    def split[A[_[_]], B[_[_]], H[_[_]]](f: A ≈> H, g: B ≈> H): ([f[_]] =>> Either[A[f], B[f]]) ≈> H =
      ∀~.mk[([f[_]] =>> Either[A[f], B[f]]) ≈> H].from(_.fold(f.apply, g.apply))
    def coidl[A[_[_]]]: ([f[_]] =>> Either[VoidHK[f], A[f]]) ≈> A = ∀~.mk[([f[_]] =>> Either[VoidHK[f], A[f]]) ≈> A].from(_.fold(identity, identity))
    def coidr[A[_[_]]]: ([f[_]] =>> Either[A[f], VoidHK[f]]) ≈> A = ∀~.mk[([f[_]] =>> Either[A[f], VoidHK[f]]) ≈> A].from(_.fold(identity, identity))
    def idl[A[_[_]]]: A ≈> ([f[_]] =>> Either[VoidHK[f], A[f]]) = ∀~.mk[A ≈> ([f[_]] =>> Either[VoidHK[f], A[f]])].from(_.asRight)
    def idr[A[_[_]]]: A ≈> ([f[_]] =>> Either[A[f], VoidHK[f]]) = ∀~.mk[A ≈> ([f[_]] =>> Either[A[f], VoidHK[f]])].from(_.asLeft)
    def braid[A[_[_]], B[_[_]]]: ([f[_]] =>> Either[A[f], B[f]]) ≈> ([f[_]] =>> Either[B[f], A[f]]) =
      ∀~.mk[([f[_]] =>> Either[A[f], B[f]]) ≈> ([f[_]] =>> Either[B[f], A[f]])].from(_.swap)
  }
}
