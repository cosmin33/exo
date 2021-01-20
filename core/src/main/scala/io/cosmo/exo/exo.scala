package io.cosmo

import io.cosmo.exo.categories.{Associative, Cartesian, Cocartesian, Distributive}
import cats.syntax._
import cats.implicits._

package object exo extends Existence with syntax {
  val InstanceOf: InstanceOfModule = InstanceOfImpl
  type InstanceOf[T] = InstanceOf.InstanceOf[T]
  @inline final def instanceOf[T](t: T): InstanceOf[T] = InstanceOf.is(t)

  type Void <: Nothing with Void.Tag

  val Forall: foralls.ForallModule = foralls.ForallImpl
  val ∀ : Forall.type = Forall
  type Forall[F[_]]   = Forall.Forall[F]
  type ∀[F[_]]        = Forall.Forall[F]

  val Forall2: foralls.Forall2Module = foralls.Forall2Impl
  val ∀∀ : Forall2.type = Forall2
  type Forall2[F[_, _]] = Forall2.Forall2[F]
  type ∀∀[F[_, _]]      = Forall2.Forall2[F]

  val Forall3: foralls.Forall3Module = foralls.Forall3Impl
  val ∀∀∀ : Forall3.type = Forall3
  type Forall3[F[_,_,_]] = Forall3.Forall3[F]
  type ∀∀∀[F[_,_,_]]     = Forall3.Forall3[F]

  val ForallK: foralls.ForallKModule = foralls.ForallKImpl
  val ∀~ : ForallK.type = ForallK
  type ForallK[A[_[_]]] = ForallK.ForallK[A]
  type ∀~[A[_[_]]]      = ForallK.ForallK[A]

  val ForallHK: foralls.ForallHKModule = foralls.ForallHKImpl
  val ∀≈ : ForallHK.type    = ForallHK
  type ForallHK[A[_[_[_]]]] = ForallHK.ForallHK[A]
  type ∀≈[A[_[_[_]]]]       = ForallHK.ForallHK[A]

  val ForallK1: foralls.ForallK1Module = foralls.ForallK1Impl
  type ForallK1[A[_[_],_]]   = ForallK1.ForallK1[A]

  val ForallK11: foralls.ForallK11Module = foralls.ForallK11Impl
  type ForallK11[A[_[_],_,_]]   = ForallK11.ForallK11[A]

  val ForallK2: foralls.ForallK2Module = foralls.ForallK2Impl
  val ∀∀~ : ForallK2.type   = ForallK2
  type ForallK2[Bi[_[_,_]]] = ForallK2.ForallK2[Bi]
  type ∀∀~[Bi[_[_,_]]]      = ForallK2.ForallK2[Bi]

  val ForallK211: foralls.ForallK211Module = foralls.ForallK211Impl
  type ForallK211[Bi[_[_,_],_,_]] = ForallK211.ForallK211[Bi]

  val ForallKBi: foralls.ForallKKModule = foralls.ForallKKImpl
  val ∀~∀~ : ForallKBi.type      = ForallKBi
  type ForallKBi[Bi[_[_], _[_]]] = ForallKBi.ForallKBi[Bi]
  type ∀~∀~[Bi[_[_], _[_]]]      = ForallKBi.ForallKBi[Bi]

  val Disjunction: DisjunctionModule = DisjunctionModuleImpl
  type Disjunction[L, R] = Disjunction.Type[L, R]
  type \/[L, R] = Disjunction[L, R]
  val \/ : Disjunction.type = Disjunction
  type -\/[L, R] = \/.TypeL[L, R]
  type \/-[L, R] = \/.TypeR[L, R]
  def  -\/[L, R](l: L): \/.TypeL[L, R] = \/.left(l)
  def  \/-[L, R](r: R): \/.TypeR[L, R] = \/.right(r)

  val Conjunction: ConjunctionModule = ConjunctionModuleImpl
  type Conjunction[L, R] = Conjunction.Type[L, R]
  type /\[L, R] = Conjunction[L, R]
  val /\ : Conjunction.type = Conjunction

  type VoidK[x] = Void
  type UnitK[x] = Unit
  type VoidHK[f[_]] = Void
  type UnitHK[f[_]] = Unit

  type Any1[α]       = Any
  type Any2[f[_]]    = Any

  // morphisms and isomorphisms
  type IsoFunK[A, B] = Iso[FunK, A, B]

  type IsoK [->[_,_], F[_], G[_]]       =  ∀[λ[a     => Iso[->, F[a], G[a]]]]
  type IsoK2[->[_,_], F[_,_], G[_,_]]   = ∀∀[λ[(a,b) => Iso[->, F[a,b], G[a,b]]]]
  type IsoHK[->[_,_], A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => Iso[->, A[f], B[f]]]]

  type <=> [A, B] = Iso[* => *, A, B]
  type ~>  [F[_], G[_]] = ∀[λ[α => F[α] =>  G[α]]]
  object ~> {
    def id[F[_]]: F ~> F = ∀.mk[F ~> F].from(identity)
    def andThen[F[_], G[_], H[_]](fg: F ~> G, gh: G ~> H): F ~> H = ∀.mk[F ~> H].fromH(t => fg[t.T].andThen(gh[t.T]))
    def initiate[F[_]]: VoidK ~> F = ∀.mk[VoidK ~> F].from(identity)
    def terminate[F[_]]: F ~> UnitK = ∀.mk[F ~> UnitK].from(_ => ())
    def distribute[F[_], G[_], H[_]]: λ[a => (F[a], Either[G[a], H[a]])] ~> λ[a => Either[(F[a], G[a]), (F[a], H[a])]] =
      ∀.mk[λ[a => (F[a], Either[G[a], H[a]])] ~> λ[a => Either[(F[a], G[a]), (F[a], H[a])]]].from(Distributive[* => *].distribute)
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
  type <~> [F[_], G[_]] = ∀[λ[α => F[α] <=> G[α]]]
  object IsoK {
    def unsafe[F[_], G[_]](fg: F ~> G, gf: G ~> F): F <~> G = ∀.mk[F <~> G].fromH(t => Iso.unsafe(fg[t.T], gf[t.T]))
  }
  val <~> : IsoK.type = IsoK
  type ~~> [F[_,_],  G[_,_]]  = ∀∀[λ[(a,b) => F[a,b] =>  G[a,b]]]
  type <~~>[F[_,_],  G[_,_]]  = ∀∀[λ[(a,b) => F[a,b] <=> G[a,b]]]
  object IsoK2 {
    def unsafe[F[_,_], G[_,_]](fg: F ~~> G, gf: G ~~> F): F <~~> G =
      ∀∀.mk[F <~~> G].fromH(t => Iso.unsafe(fg[t.A, t.B], gf[t.A, t.B]))
  }
  val <~~> : IsoK2.type = IsoK2
  type ≈>  [A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => A[f] =>  B[f]]]
  object ≈> {
    def id[A[_[_]]]: A ≈> A = ∀~.mk[A ≈> A].from(identity)
    def andThen[A[_[_]], B[_[_]], C[_[_]]](fg: A ≈> B, gh: B ≈> C): A ≈> C =
      ∀~.mk[A ≈> C].fromH(t => fg.apply[t.T].andThen(gh.apply[t.T]))
    def initiate [A[_[_]]]: VoidHK ≈> A = ∀~.mk[VoidHK ≈> A].from(identity)
    def terminate[A[_[_]]]: A ≈> UnitHK = ∀~.mk[A ≈> UnitHK].from(_ => ())
    def distribute[A[_[_]], B[_[_]], C[_[_]]]: λ[f[_] => (A[f], Either[B[f], C[f]])] ≈> λ[f[_] => Either[(A[f], B[f]), (A[f], C[f])]] =
      ∀~.mk[λ[f[_] => (A[f], Either[B[f], C[f]])] ≈> λ[f[_] => Either[(A[f], B[f]), (A[f], C[f])]]].from(Distributive[* => *].distribute)
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
  type <≈> [A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => A[f] <=> B[f]]]
  type ≈≈>  [A[_[_],_[_]], B[_[_],_[_]]] = ∀~∀~[λ[(f[_],g[_]) => A[f, g] =>  B[f, g]]]
  type <≈≈> [A[_[_],_[_]], B[_[_],_[_]]] = ∀~∀~[λ[(f[_],g[_]) => A[f, g] <=> B[f, g]]]

  //type Exofun[==>[_,_], -->[_,_], F[_]] = ==> ~~> λ[(a, b) => F[a] --> F[b]]

}
