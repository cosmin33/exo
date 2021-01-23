package io.cosmo.exo.internalstuff

import cats.implicits._
import io.cosmo.exo.categories.{Associative, Cartesian, Cocartesian, Distributive}
import io.cosmo.exo.{UnitHK, VoidHK, ∀~, ≈>}

private[exo] trait FunctionHKObject {
  def id[A[_[_]]]: A ≈> A = ∀~.mk[A ≈> A].from(identity)
  def andThen[A[_[_]], B[_[_]], C[_[_]]](fg: A ≈> B, gh: B ≈> C): A ≈> C =
    ∀~.mk[A ≈> C].fromH(t => fg.apply[t.T].andThen(gh.apply[t.T]))
  def initiate [A[_[_]]]: VoidHK ≈> A = ∀~.mk[VoidHK ≈> A].from(identity)
  def terminate[A[_[_]]]: A ≈> UnitHK = ∀~.mk[A ≈> UnitHK].from(_ => ())
  def distribute[A[_[_]], B[_[_]], C[_[_]]]: λ[f[_] => (A[f], Either[B[f], C[f]])] ≈> λ[f[_] => Either[(A[f], B[f]), (A[f], C[f])]] =
    ∀~.mk[λ[f[_] => (A[f], Either[B[f], C[f]])] ≈> λ[f[_] => Either[(A[f], B[f]), (A[f], C[f])]]].from(Distributive[* => *, Tuple2, Either].distribute)
  object product {
    def associate  [A[_[_]], B[_[_]], C[_[_]]]: λ[f[_] => ((A[f], B[f]), C[f])] ≈> λ[f[_] => (A[f], (B[f], C[f]))] =
      ∀~.mk[λ[f[_] => ((A[f], B[f]), C[f])] ≈> λ[f[_] => (A[f], (B[f], C[f]))]].from(Associative[* => *, (*, *)].associate)
    def diassociate[A[_[_]], B[_[_]], C[_[_]]]: λ[f[_] => (A[f], (B[f], C[f]))] ≈> λ[f[_] => ((A[f], B[f]), C[f])] =
      ∀~.mk[λ[f[_] => (A[f], (B[f], C[f]))] ≈> λ[f[_] => ((A[f], B[f]), C[f])]].from(Associative[* => *, (*, *)].diassociate)
    def bimap[A[_[_]], B[_[_]], X[_[_]], Y[_[_]]](fg: A ≈> B, xy: X ≈> Y): λ[f[_] => (A[f], X[f])] ≈> λ[f[_] => (B[f], Y[f])] =
      ∀~.mk[λ[f[_] => (A[f], X[f])] ≈> λ[f[_] => (B[f], Y[f])]].fromH(t => Associative[* => *, (*, *)].grouped(fg[t.T], xy[t.T]))
    def fst[A[_[_]], B[_[_]]]: λ[f[_] => (A[f], B[f])] ≈> A = ∀~.mk[λ[f[_] => (A[f], B[f])] ≈> A].from(fg => fg._1)
    def snd[A[_[_]], B[_[_]]]: λ[f[_] => (A[f], B[f])] ≈> B = ∀~.mk[λ[f[_] => (A[f], B[f])] ≈> B].from(fg => fg._2)
    def diag[A[_[_]]]: A ≈> λ[f[_] => (A[f], A[f])] = ∀~.mk[A ≈> λ[f[_] => (A[f], A[f])]].from(a => (a, a))

    def merge[A[_[_]], B[_[_]], C[_[_]]](f: A ≈> B, g: A ≈> C): A ≈> λ[f[_] => (B[f], C[f])] =
      ∀~.mk[A ≈> λ[f[_] => (B[f], C[f])]].fromH(t => Cartesian[* => *, (*, *)].&&&(f[t.T], g[t.T]))
    def idl  [A[_[_]]]: λ[f[_] => (UnitHK[f], A[f])] ≈> A = ∀~.mk[λ[f[_] => (UnitHK[f], A[f])] ≈> A].from(_._2)
    def coidl[A[_[_]]]: A ≈> λ[f[_] => (UnitHK[f], A[f])] = ∀~.mk[A ≈> λ[f[_] => (UnitHK[f], A[f])]].from(((), _))
    def idr  [A[_[_]]]: λ[f[_] => (A[f], UnitHK[f])] ≈> A = ∀~.mk[λ[f[_] => (A[f], UnitHK[f])] ≈> A].from(_._1)
    def coidr[A[_[_]]]: A ≈> λ[f[_] => (A[f], UnitHK[f])] = ∀~.mk[A ≈> λ[f[_] => (A[f], UnitHK[f])]].from((_, ()))
    def braid[A[_[_]], B[_[_]]]: λ[f[_] => (A[f], B[f])] ≈> λ[f[_] => (B[f], A[f])] =
      ∀~.mk[λ[f[_] => (A[f], B[f])] ≈> λ[f[_] => (B[f], A[f])]].from(_.swap)
  }
  object coproduct {
    def diassociate[A[_[_]], B[_[_]], C[_[_]]]: λ[f[_] => Either[Either[A[f], B[f]], C[f]]] ≈> λ[f[_] => Either[A[f], Either[B[f], C[f]]]] =
      ∀~.mk[λ[f[_] => Either[Either[A[f], B[f]], C[f]]] ≈> λ[f[_] => Either[A[f], Either[B[f], C[f]]]]].from(Associative[* => *, Either].associate)
    def associate[A[_[_]], B[_[_]], C[_[_]]]: λ[f[_] => Either[A[f], Either[B[f], C[f]]]] ≈> λ[f[_] => Either[Either[A[f], B[f]], C[f]]] =
      ∀~.mk[λ[f[_] => Either[A[f], Either[B[f], C[f]]]] ≈> λ[f[_] => Either[Either[A[f], B[f]], C[f]]]].from(Associative[* => *, Either].diassociate)
    def bimap[A[_[_]], B[_[_]], X[_[_]], Y[_[_]]](fg: A ≈> B, xy: X ≈> Y): λ[f[_] => Either[A[f], X[f]]] ≈> λ[f[_] => Either[B[f], Y[f]]] =
      ∀~.mk[λ[f[_] => Either[A[f], X[f]]] ≈> λ[f[_] => Either[B[f], Y[f]]]].fromH(t => Associative[* => *, Either].grouped(fg[t.T], xy[t.T]))
    def inl[A[_[_]], B[_[_]]]: A ≈> λ[f[_] => Either[A[f], B[f]]] = ∀~.mk[A ≈> λ[f[_] => Either[A[f], B[f]]]].from(_.asLeft)
    def inr[A[_[_]], B[_[_]]]: B ≈> λ[f[_] => Either[A[f], B[f]]] = ∀~.mk[B ≈> λ[f[_] => Either[A[f], B[f]]]].from(_.asRight)
    def codiag[A[_[_]]]: λ[f[_] => Either[A[f], A[f]]] ≈> A = ∀~.mk[λ[f[_] => Either[A[f], A[f]]] ≈> A].from(_.fold(identity, identity))
    def split[A[_[_]], B[_[_]], C[_[_]]](f: A ≈> C, g: B ≈> C): λ[f[_] => Either[A[f], B[f]]] ≈> C =
      ∀~.mk[λ[f[_] => Either[A[f], B[f]]] ≈> C].fromH(t => Cocartesian[* => *, Either].|||(f[t.T], g[t.T]))
    def coidl[A[_[_]]]: λ[f[_] => Either[VoidHK[f], A[f]]] ≈> A = ∀~.mk[λ[f[_] => Either[VoidHK[f], A[f]]] ≈> A].from(_.fold(identity, identity))
    def idl  [A[_[_]]]: A ≈> λ[f[_] => Either[VoidHK[f], A[f]]] = ∀~.mk[A ≈> λ[f[_] => Either[VoidHK[f], A[f]]]].from(_.asRight)
    def coidr[A[_[_]]]: λ[f[_] => Either[A[f], VoidHK[f]]] ≈> A = ∀~.mk[λ[f[_] => Either[A[f], VoidHK[f]]] ≈> A].from(_.fold(identity, identity))
    def idr  [A[_[_]]]: A ≈> λ[f[_] => Either[A[f], VoidHK[f]]] = ∀~.mk[A ≈> λ[f[_] => Either[A[f], VoidHK[f]]]].from(_.asLeft)
    def braid[A[_[_]], B[_[_]]]: λ[f[_] => Either[A[f], B[f]]] ≈> λ[f[_] => Either[B[f], A[f]]] =
      ∀~.mk[λ[f[_] => Either[A[f], B[f]]] ≈> λ[f[_] => Either[B[f], A[f]]]].from(_.swap)
  }
}
