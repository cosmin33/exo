package io.cosmo

import cats.implicits._
import io.cosmo.exo.Iso.{HasIso, HasIsoK}
import io.cosmo.exo.categories.{Associative, Cartesian, Cocartesian, Distributive, Dual, Trivial}
import io.cosmo.exo.typeclasses.TypeK

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

  type VoidK[x]     = Void
  type VoidK2[x,y]  = Void
  type VoidHK[f[_]] = Void
  type UnitK[x]     = Unit
  type UnitK2[x,y]  = Unit
  type UnitHK[f[_]] = Unit
  type AnyK[x]      = Any
  type AnyK2[x,y]   = Any
  type AnyHK[f[_]]  = Any

  // morphisms and isomorphisms
  type IsoFunK[A, B] = Iso[FunK, A, B]
  object IsoFunK {
    def apply[F[_], G[_]](i: F <~> G): IsoFunK[TypeK[F], TypeK[G]] = FunK.impIsoFunK(i)
  }

  type IsoK [->[_,_], F[_], G[_]]       =  ∀[λ[a     => Iso[->, F[a], G[a]]]]
  type IsoK2[->[_,_], F[_,_], G[_,_]]   = ∀∀[λ[(a,b) => Iso[->, F[a,b], G[a,b]]]]
  type IsoHK[->[_,_], A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => Iso[->, A[f], B[f]]]]

  type <==[A, B] = Dual[* => *, A, B]
  type <=>[A, B] = Iso[* => *, A, B]
  object <=> {
    def apply[A]: A <=> A = Iso.refl
    def apply[A, B](implicit h: HasIso[* => *, A, B]): A <=> B = h.iso
    def unsafe[A, B](ab: A => B, ba: B => A): A <=> B = Iso.unsafe(ab, ba)
  }
  type ~>[F[_], G[_]] = ∀[λ[α => F[α] => G[α]]]
  object ~> extends internalstuff.FunctionKObject
  type <~ [F[_], G[_]] = ∀[λ[α => Dual[* => *, F[α], G[α]]]]
  type <~>[F[_], G[_]] = ∀[λ[α => F[α] <=> G[α]]]
  object <~> {
    def apply[F[_]]: F <~> F = apply[F, F]
    def apply[F[_], G[_]](implicit h: HasIsoK[* => *, F, G]): F <~> G = h.iso
    def unsafe[F[_], G[_]](fg: F ~> G, gf: G ~> F): F <~> G = ∀.mk[F <~> G].from(Iso.unsafe(fg.apply, gf.apply))
  }
  type ~~> [F[_,_], G[_,_]] = ∀∀[λ[(a,b) => F[a,b] =>  G[a,b]]]
  object ~~> extends internalstuff.FunctionK2Object
  type <~~ [F[_,_], G[_,_]] = ∀∀[λ[(a,b) => Dual[* => *, F[a,b], G[a,b]]]]
  type <~~>[F[_,_], G[_,_]] = ∀∀[λ[(a,b) => F[a,b] <=> G[a,b]]]
  object <~~> {
    def apply[F[_,_]]: F <~~> F = ∀∀.mk[F <~~> F].from(Iso.unsafe(identity, identity))
    def unsafe[F[_,_], G[_,_]](fg: F ~~> G, gf: G ~~> F): F <~~> G = ∀∀.mk[F <~~> G].from(Iso.unsafe(fg.apply, gf.apply))
  }
  type ≈>  [A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => A[f] =>  B[f]]]
  type <≈  [A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => Dual[* => *, A[f], B[f]]]]
  object ≈> extends internalstuff.FunctionHKObject
  type <≈> [A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => A[f] <=> B[f]]]
  object <≈> {
    def apply[A[_[_]]]: A <≈> A = ∀~.mk[A <≈> A].from(Iso.unsafe(identity, identity))
    def unsafe[A[_[_]], B[_[_]]](ab: A ≈> B, ba: B ≈> A): A <≈> B = ∀~.mk[A <≈> B].from(Iso.unsafe(ab.apply, ba.apply))
  }
  type ≈≈>  [A[_[_],_[_]], B[_[_],_[_]]] = ∀~∀~[λ[(f[_],g[_]) => A[f, g] =>  B[f, g]]]
  type <≈≈  [A[_[_],_[_]], B[_[_],_[_]]] = ∀~∀~[λ[(f[_],g[_]) => Dual[* => *, A[f, g], B[f, g]]]]
  type <≈≈> [A[_[_],_[_]], B[_[_],_[_]]] = ∀~∀~[λ[(f[_],g[_]) => A[f, g] <=> B[f, g]]]

}
