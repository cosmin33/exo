package io.cosmo

import io.cosmo.exo.typeclasses.TypeF

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
  type ForallHK[A[_[_[_]]]] = ForallHK.ForallHK[A]

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
  val (\/): Disjunction.type = Disjunction
  type -\/[L, R] = \/.TypeL[L, R]
  type \/-[L, R] = \/.TypeR[L, R]
  def  -\/[L, R](l: L): \/.TypeL[L, R] = \/.left(l)
  def  \/-[L, R](r: R): \/.TypeR[L, R] = \/.right(r)

  val Conjunction: ConjunctionModule = ConjunctionModuleImpl
  type Conjunction[L, R] = Conjunction.Type[L, R]
  type /\[L, R] = Conjunction[L, R]
  val (/\): Conjunction.type = Conjunction

  type Any1[α]       = α => Any
  type Any2[f[_]]    = Any1[Any1[Any]]

  // morphisms and isomorphisms
  //type FunK  [->[_,_], F[_],    G[_]]    =  ∀[λ[ᵒ     => F[ᵒ] -> G[ᵒ]]]
  //type BifunK[->[_,_], F[_,_],  G[_,_]]  = ∀∀[λ[(a,b) => F[a,b] -> G[a,b]]]
  //type FunHK [->[_,_], A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => A[f] -> B[f]]]

  type IsoFunK[A, B] = Iso[FunK, A, B]

  type IsoK [->[_,_], F[_], G[_]]       =  ∀[λ[a     => Iso[->, F[a], G[a]]]]
  type IsoK2[->[_,_], F[_,_], G[_,_]]   = ∀∀[λ[(a,b) => Iso[->, F[a,b], G[a,b]]]]
  type IsoHK[->[_,_], A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => Iso[->, A[f], B[f]]]]

  type <=> [A, B] = Iso[* => *, A, B]
  type ~>  [F[_], G[_]] = Forall.Forall[λ[ᵒ => F[ᵒ] =>  G[ᵒ]]]
  type <~> [F[_], G[_]] = Forall.Forall[λ[a => F[a] <=> G[a]]]
  object <~> {
    def unsafe[F[_], G[_]](fg: F ~> G, gf: G ~> F): F <~> G = ∀.mk[F <~> G].fromH(t => Iso.unsafe(fg[t.T], gf[t.T]))
  }
  type ~~> [F[_,_],  G[_,_]]  = ∀∀[λ[(a,b) => F[a,b] =>  G[a,b]]]
  type <~~>[F[_,_],  G[_,_]]  = ∀∀[λ[(a,b) => F[a,b] <=> G[a,b]]]
  object <~~> {
    def unsafe[F[_,_], G[_,_]](fg: F ~~> G, gf: G ~~> F): F <~~> G =
      ∀∀.mk[F <~~> G].fromH(t => Iso.unsafe(fg[t.T1, t.T2], gf[t.T1, t.T2]))
  }
  type ≈>  [A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => A[f] =>  B[f]]]
  type <≈> [A[_[_]], B[_[_]]] = ∀~[λ[f[_]  => A[f] <=> B[f]]]

  type Exofun[==>[_,_], -->[_,_], F[_]] = ==> ~~> λ[(a, b) => F[a] --> F[b]]

}
