package io.cosmo.exo

import io.cosmo.exo.evidence._

object foralls {

  private[exo] sealed trait ForallModule {
    type Forall[F[_]]
    type ∀[F[_]] = Forall[F]

    trait Prototype[F[_]] {
      def apply[X]: F[X]
      final def make: ∀[F] = from(this)
    }

    def specialize[F[_], A](v: ∀[F]): F[A]
    def instantiation[F[_], A]: ∀[F] <~< F[A]
    def vacuous[A]: A <~< ∀[λ[α => A]]
    def monotonicity[F[_], G[_]](ev: ∀[λ[α => F[α] <~< G[α]]]): ∀[F] <~< ∀[G]
    def from[F[_]](p: Prototype[F]): ∀[F]
    def of[F[_]]: MkForall[F]
    def mk[X](implicit u: Unapply[X]): MkForall[u.F] = of[u.F]

    trait MkForall[F[_]] extends Any {
      type T
      def from(ft: F[T]): ∀[F]
      def apply(ft: F[T]): ∀[F] = from(ft)
      def fromH(ft: TypeHolder[T] => F[T]): Forall[F] = from(ft(TypeHolder[T]))
    }

    trait Unapply[X] { type F[_] }
    object Unapply {
      implicit def unapply[G[_]]: Unapply[∀[G]] { type F[A] = G[A] } = new Unapply[∀[G]] { type F[A] = G[A] }
    }
  }

  private[exo] object ForallImpl extends ForallModule {
    type Forall[F[_]] = F[Any]

    def specialize[F[_], A](f: ∀[F]): F[A]    = f.asInstanceOf[F[A]]
    def instantiation[F[_], A]: ∀[F] <~< F[A] = As.refl[Any].asInstanceOf[∀[F] <~< F[A]]
    def vacuous[A]: A <~< ∀[λ[α => A]]        = As.refl[A]
    def monotonicity[F[_], G[_]](ev: ∀[λ[α => F[α] <~< G[α]]]): ∀[F] <~< ∀[G] = As.refl[Any].asInstanceOf[∀[F] <~< ∀[G]]
    def from[F[_]](p: Prototype[F]): ∀[F]     = p[Any]
    def of[F[_]]: MkForall[F] = new MkForallImpl[F]
  }

  private[exo] sealed trait Forall2Module {
    type Forall2[F[_, _]]
    type ∀∀[F[_, _]] = Forall2[F]

    trait Prototype[F[_, _]] {
      def apply[A, B]: F[A, B]
      final def make: ∀∀[F] = from(this)
    }

    def specialize[F[_, _], A, B](f: ∀∀[F]): F[A, B]
    def instantiation[F[_,_], A, B]: ∀∀[F] <~< F[A, B]
    def monotonicity[F[_,_], G[_,_]](ev: ∀∀[λ[(a,b) => F[a,b] <~< G[a,b]]]): ∀∀[F] <~< ∀∀[G]
    def from[F[_, _]](p: Prototype[F]): ∀∀[F]
    def of[F[_, _]]: MkForall2[F]
    def mk[X](implicit u: Unapply[X]): MkForall2[u.F] = of[u.F]

    sealed trait MkForall2[F[_, _]] extends Any {
      type T
      type U
      def from(ft: F[T, U]): ∀∀[F]
      def apply(ft: F[T, U]): ∀∀[F] = from(ft)
      def fromH(ft: TypeHolder2[T, U] => F[T, U]): Forall2[F] = from(ft(TypeHolder2[T, U]))
    }

    trait Unapply[X] { type F[_, _] }
    object Unapply {
      implicit def unapply[G[_, _]]: Unapply[∀∀[G]] { type F[A, B] = G[A, B] } = new Unapply[∀∀[G]] { type F[A, B] = G[A, B] } 
    }
  }

  private[exo] object Forall2Impl extends Forall2Module {
    type Forall2[F[_, _]] = F[Any, Any]

    def specialize[F[_, _], A, B](f: ∀∀[F]): F[A, B] = f.asInstanceOf[F[A, B]]
    def instantiation[F[_,_], A, B]: ∀∀[F] <~< F[A, B] = As.refl[(Any, Any)].asInstanceOf[∀∀[F] <~< F[A, B]]
    def monotonicity[F[_,_], G[_,_]](ev: ∀∀[λ[(a,b) => F[a,b] <~< G[a,b]]]): ∀∀[F] <~< ∀∀[G] =
      As.refl[(Any, Any)].asInstanceOf[∀∀[F] <~< ∀∀[G]]
    def from[F[_, _]](p: Prototype[F]): ∀∀[F] = p[Any, Any]
    def of[F[_, _]]: MkForall2[F] = new MkForall2Impl[F]
  }

  private[exo] sealed trait Forall3Module {
    type Forall3[F[_,_,_]]
    type ∀∀∀[F[_,_,_]] = Forall3[F]

    trait Prototype[F[_,_,_]] {
      def apply[A, B, C]: F[A, B, C]
      final def make: ∀∀∀[F] = from(this)
    }

    def specialize[F[_,_,_], A, B, C](f: ∀∀∀[F]): F[A, B, C]
    def instantiation[F[_,_,_], A, B, C]: ∀∀∀[F] <~< F[A, B, C]
    def monotonicity[F[_,_,_], G[_,_,_]](ev: ∀∀∀[λ[(a,b,c) => F[a,b,c] <~< G[a,b,c]]]): ∀∀∀[F] <~< ∀∀∀[G]
    def from[F[_,_,_]](p: Prototype[F]): ∀∀∀[F]
    def of[F[_,_,_]]: MkForall3[F]
    def mk[X](implicit u: Unapply[X]): MkForall3[u.F] = of[u.F]

    sealed trait MkForall3[F[_,_,_]] extends Any {
      type A
      type B
      type C
      def from(ft: F[A, B, C]): ∀∀∀[F]
      def apply(ft: F[A, B, C]): ∀∀∀[F] = from(ft)
      def fromH(ft: TypeHolder3[A, B, C] => F[A, B, C]): Forall3[F] = from(ft(TypeHolder3[A, B, C]))
    }

    trait Unapply[X] { type F[_,_,_] }
    object Unapply {
      implicit def unapply[G[_,_,_]]: Unapply[∀∀∀[G]] {type F[A, B, C] = G[A, B, C]} = new Unapply[∀∀∀[G]] {type F[A, B, C] = G[A, B, C]}
    }
  }

  private[exo] object Forall3Impl extends Forall3Module {
    type Forall3[F[_,_,_]] = F[Any, Any, Any]

    def specialize[F[_,_,_], A, B, C](f: ∀∀∀[F]): F[A, B, C] = f.asInstanceOf[F[A, B, C]]
    def instantiation[F[_,_,_], A, B, C]: ∀∀∀[F] <~< F[A, B, C] =
      As.refl[(Any, Any, Any)].asInstanceOf[∀∀∀[F] <~< F[A, B, C]]
    def monotonicity[F[_,_,_], G[_,_,_]](ev: ∀∀∀[λ[(a,b,c) => F[a,b,c] <~< G[a,b,c]]]): ∀∀∀[F] <~< ∀∀∀[G] =
      As.refl[(Any, Any, Any)].asInstanceOf[∀∀∀[F] <~< ∀∀∀[G]]
    def from[F[_,_,_]](p: Prototype[F]): ∀∀∀[F] = p[Any, Any, Any]
    def of[F[_,_,_]]: MkForall3[F] = new MkForall3Impl[F]
  }

  private[exo] sealed trait ForallKModule {
    type ForallK[Alg[_[_]]]
    type ∀~[Alg[_[_]]] = ForallK[Alg]

    trait Prototype[Alg[_[_]]] {
      def apply[F[_]]: Alg[F]
      final def make: ∀~[Alg] = from(this)
    }

    def specialize[Alg[_[_]], F[_]](v: ∀~[Alg]): Alg[F]
    def instantiation[Alg[_[_]], F[_]]: ∀~[Alg] <~< Alg[F]
    def monotonicity[A1[_[_]], B1[_[_]]](ev: ∀~[λ[f[_] => A1[f] <~< B1[f]]]): ∀~[A1] <~< ∀~[B1]
    def from[Alg[_[_]]](p: Prototype[Alg]): ∀~[Alg]
    def of[Alg[_[_]]]: MkForallK[Alg]
    def mk[x](implicit u: Unapply[x]): MkForallK[u.A] = of[u.A]

    trait MkForallK[Alg[_[_]]] extends Any {
      type T[_]
      def from(ft: Alg[T]): ∀~[Alg]
      def apply(ft: Alg[T]): ∀~[Alg] = from(ft)
      def fromH(ft: TypeHolderK[T] => Alg[T]): ForallK[Alg] = from(ft(TypeHolderK[T]))
    }

    trait Unapply[X] { type A[_[_]] }
    object Unapply {
      implicit def unapply[B[_[_]]]: Unapply[∀~[B]] { type A[f[_]] = B[f] } = new Unapply[∀~[B]] { type A[f[_]] = B[f] }
    }
  }

  private[exo] object ForallKImpl extends ForallKModule {
    type ForallK[A[_[_]]] = A[λ[α => Any]]

    def specialize[Alg[_[_]], F[_]](f: ∀~[Alg]): Alg[F] = f.asInstanceOf[Alg[F]]
    def instantiation[Alg[_[_]], F[_]]: ∀~[Alg] <~< Alg[F] = As.refl[Any].asInstanceOf[∀~[Alg] <~< Alg[F]]
    def monotonicity[A1[_[_]], B1[_[_]]](ev: ∀~[λ[f[_] => A1[f] <~< B1[f]]]): ∀~[A1] <~< ∀~[B1] =
      As.refl[Any].asInstanceOf[∀~[A1] <~< ∀~[B1]]
    def from[Alg[_[_]]](p: Prototype[Alg]): ∀~[Alg] = p[λ[α => Any]]
    def of[Alg[_[_]]]: MkForallK[Alg] = new MkForallKImpl[Alg]
  }
  
  private[exo] sealed trait ForallHKModule {
    type ForallHK[Alg[_[_[_]]]]

    trait Prototype[Alg[_[_[_]]]] {
      def apply[F[_[_]]]: Alg[F]
      final def make: ForallHK[Alg] = from(this)
    }

    def specialize[Alg[_[_[_]]], F[_[_]]](v: ForallHK[Alg]): Alg[F]
    def instantiation[Alg[_[_[_]]], F[_[_]]]: ForallHK[Alg] <~< Alg[F]
    def monotonicity[A1[_[_[_]]], B1[_[_[_]]]](ev: ForallHK[λ[f[_[_]] => A1[f] <~< B1[f]]]): ForallHK[A1] <~< ForallHK[B1]
    def from[Alg[_[_[_]]]](p: Prototype[Alg]): ForallHK[Alg]
    def of[Alg[_[_[_]]]]: MkForallHK[Alg]
    def mk[x](implicit u: Unapply[x]): MkForallHK[u.A] = of[u.A]

    trait MkForallHK[Alg[_[_[_]]]] extends Any {
      type T[_[_]]
      def from(ft: Alg[T]): ForallHK[Alg]
      def apply(ft: Alg[T]): ForallHK[Alg] = from(ft)
      def fromH(ft: TypeHolderHK[T] => Alg[T]): ForallHK[Alg] = from(ft(TypeHolderHK[T]))
    }

    trait Unapply[X] { type A[_[_[_]]] }
    object Unapply {
      implicit def unapply[B[_[_[_]]]]: Unapply[ForallHK[B]] { type A[f[_[_]]] = B[f] } =
        new Unapply[ForallHK[B]] { type A[f[_[_]]] = B[f] }
    }
  }

  private[exo] object ForallHKImpl extends ForallHKModule {
    type ForallHK[A[_[_[_]]]] = A[λ[α[_] => Any]]

    def specialize[Alg[_[_[_]]], F[_[_]]](f: ForallHK[Alg]): Alg[F] = f.asInstanceOf[Alg[F]]
    def instantiation[Alg[_[_[_]]], F[_[_]]]: ForallHK[Alg] <~< Alg[F] =
      As.refl[Any].asInstanceOf[ForallHK[Alg] <~< Alg[F]]
    def monotonicity[A1[_[_[_]]], B1[_[_[_]]]](ev: ForallHK[λ[f[_[_]] => A1[f] <~< B1[f]]]): ForallHK[A1] <~< ForallHK[B1] =
      As.refl[Any].asInstanceOf[ForallHK[A1] <~< ForallHK[B1]]
    def from[Alg[_[_[_]]]](p: Prototype[Alg]): ForallHK[Alg] = p[λ[α[_] => Any]]
    def of[Alg[_[_[_]]]]: MkForallHK[Alg] = new MkForallHKImpl[Alg]
  }

  private[exo] sealed trait ForallK1Module {
    type ForallK1[Alg[_[_],_]]

    trait Prototype[Alg[_[_],_]] {
      def apply[F[_], A]: Alg[F, A]
      final def make: ForallK1[Alg] = from(this)
    }

    def specialize[Alg[_[_],_], F[_], A](v: ForallK1[Alg]): Alg[F, A]
    def instantiation[Alg[_[_],_], F[_], A]: ForallK1[Alg] <~< Alg[F, A]
    def monotonicity[A1[_[_],_], A2[_[_],_]](ev: ForallK1[λ[(f[_],a) => A1[f,a] <~< A2[f,a]]]): ForallK1[A1] <~< ForallK1[A2]
    def from[Alg[_[_],_]](p: Prototype[Alg]): ForallK1[Alg]
    def of[Alg[_[_],_]]: MkForallK1[Alg]
    def mk[x](implicit u: Unapply[x]): MkForallK1[u.A] = of[u.A]

    trait MkForallK1[Alg[_[_],_]] extends Any {
      type T[_]
      type X
      def from (ft: Alg[T, X]): ForallK1[Alg]
      def apply(ft: Alg[T, X]): ForallK1[Alg] = from(ft)
    }

    trait Unapply[X] { type A[_[_],_] }
    object Unapply {
      implicit def unapply[B[_[_],_]]: Unapply[ForallK1[B]] { type A[f[_],a] = B[f,a] } = new Unapply[ForallK1[B]] { type A[f[_],a] = B[f,a] }
    }

  }

  private[exo] object ForallK1Impl extends ForallK1Module {
    type ForallK1[A[_[_],_]] = A[Any1, Any]

    def specialize[Alg[_[_],_], F[_], A](f: ForallK1[Alg]): Alg[F, A] = f.asInstanceOf[Alg[F, A]]
    def instantiation[Alg[_[_], _], F[_], A]: ForallK1[Alg] <~< Alg[F, A] = As.refl[A => Any].asInstanceOf
    def monotonicity[A1[_[_], _], A2[_[_], _]](ev: ForallK1[λ[(f[_],a) => A1[f,a] <~< A2[f,a]]]):ForallK1[A1] <~< ForallK1[A2] =
      As.refl[Any].asInstanceOf
    def from[Alg[_[_],_]](p: Prototype[Alg]): ForallK1[Alg] = p[Any1, Any]
    def of[Alg[_[_],_]]: MkForallK1[Alg] = new MkForallK1Impl[Alg]
  }

  private[exo] trait ForallK2Module {
    type ForallK2[A[_[_,_]]]
    type ∀∀~[Bi[_[_,_]]] = ForallK2[Bi]

    trait Prototype[Bi[_[_,_]]] {
      def apply[F[_,_]]: Bi[F]
      final def make: ∀∀~[Bi] = from(this)
    }

    def specialize[Bi[_[_,_]], F[_,_]](f: ∀∀~[Bi]): Bi[F]
    def instantiation[Bi[_[_,_]], F[_,_]]: ∀∀~[Bi] <~< Bi[F]
    def monotonicity[A1[_[_,_]], A2[_[_,_]]](ev: ∀∀~[λ[b[_,_] => A1[b] <~< A2[b]]]): ∀∀~[A1] <~< ∀∀~[A2]
    def from[Bi[_[_,_]]](p: Prototype[Bi]): ∀∀~[Bi]
    def of[Bi[_[_,_]]]: MkForallK2[Bi]
    def mk[X](implicit u: Unapply[X]): MkForallK2[u.Bi] = of[u.Bi]

    sealed trait MkForallK2[Bi[_[_,_]]] extends Any {
      type T[_,_]
      def from(ft: Bi[T]): ∀∀~[Bi]
      def apply(ft: Bi[T]): ∀∀~[Bi] = from(ft)
    }

    trait Unapply[X] { type Bi[_[_,_]] }
    object Unapply {
      implicit def unapply[Ci[_[_,_]]]: Unapply[∀∀~[Ci]] { type Bi[F[_,_]] = Ci[F] } = new Unapply[∀∀~[Ci]] { type Bi[F[_,_]] = Ci[F] }
    }
  }

  private[exo] object ForallK2Impl extends ForallK2Module {
    type AnyP[x,y] = Any
    type ForallK2[Bi[_[_,_]]] = Bi[AnyP]

    def specialize[Bi[_[_,_]], F[_,_]](f: ∀∀~[Bi]): Bi[F] = f.asInstanceOf[Bi[F]]
    def instantiation[Bi[_[_,_]], F[_,_]]: ∀∀~[Bi] <~< Bi[F] = As.refl[Any].asInstanceOf
    def monotonicity[A1[_[_,_]], A2[_[_,_]]](ev: ∀∀~[λ[b[_,_] => A1[b] <~< A2[b]]]): ∀∀~[A1] <~< ∀∀~[A2] =
      As.refl[Any].asInstanceOf
    def from[Bi[_[_,_]]](p: Prototype[Bi]): ∀∀~[Bi] = p[Any]
    def of[Bi[_[_,_]]]: MkForallK2[Bi] = new MkForallK2Impl[Bi]
  }

  private[exo] sealed trait ForallK11Module {
    type ForallK11[Alg[_[_],_,_]]
    type ∀~~[Alg[_[_],_,_]] = ForallK11[Alg]

    trait Prototype[Alg[_[_],_,_]] {
      def apply[F[_], A, B]: Alg[F, A, B]
      final def make: ∀~~[Alg] = from(this)
    }

    def specialize[Alg[_[_],_,_], F[_], A, B](v: ∀~~[Alg]): Alg[F, A, B]
    def instantiation[Alg[_[_],_,_], F[_], A, B]: ∀~~[Alg] <~< Alg[F, A, B]
    def monotonicity[A1[_[_],_,_], A2[_[_],_,_]](ev: ∀~~[λ[(f[_],a,b) => A1[f,a,b] <~< A2[f,a,b]]]): ∀~~[A1] <~< ∀~~[A2]
    def from[Alg[_[_],_,_]](p: Prototype[Alg]): ∀~~[Alg]
    def of[Alg[_[_],_,_]]: MkForallK11[Alg]
    def mk[x](implicit u: Unapply[x]): MkForallK11[u.A] = of[u.A]

    trait MkForallK11[Alg[_[_],_,_]] extends Any {
      type T[_]
      type X
      type Y
      def from (ft: Alg[T, X, Y]): ∀~~[Alg]
      def apply(ft: Alg[T, X, Y]): ∀~~[Alg] = from(ft)
    }

    trait Unapply[X] { type A[_[_],_,_] }
    object Unapply {
      implicit def unapply[B[_[_],_,_]]: Unapply[∀~~[B]] { type A[f[_],a,b] = B[f,a,b] } = new Unapply[∀~~[B]] { type A[f[_],a,b] = B[f,a,b] }
    }
  }

  private[exo] object ForallK11Impl extends ForallK11Module {
    type ForallK11[A[_[_],_,_]] = A[* => Any, Any, Any]

    def specialize[Alg[_[_],_,_], F[_], A, B](f: ForallK11[Alg]): Alg[F, A, B] = f.asInstanceOf[Alg[F, A, B]]
    def instantiation[Alg[_[_],_,_], F[_], A, B]: ∀~~[Alg] <~< Alg[F, A, B] = As.refl[Any].asInstanceOf
    def monotonicity[A1[_[_],_,_], A2[_[_],_,_]](ev: ∀~~[λ[(f[_],a,b) => A1[f,a,b] <~< A2[f,a,b]]]): ∀~~[A1] <~< ∀~~[A2] =
      As.refl[Any].asInstanceOf
    def from[Alg[_[_],_,_]](p: Prototype[Alg]): ForallK11[Alg] = p[* => Any, Any, Any]
    def of[Alg[_[_],_,_]]: MkForallK11[Alg] = new MkForallK11Impl[Alg]
  }

  private[exo] trait ForallKKModule {
    type ForallKBi[Bi[_[_], _[_]]]
    type ∀~∀~[Bi[_[_], _[_]]] = ForallKBi[Bi]

    trait Prototype[Bi[_[_], _[_]]] {
      def apply[F[_], G[_]]: Bi[F, G]
      final def make: ∀~∀~[Bi] = from(this)
    }

    def specialize[Bi[_[_], _[_]], F[_], G[_]](f: ∀~∀~[Bi]): Bi[F, G]
    def from[Bi[_[_], _[_]]](p: Prototype[Bi]): ∀~∀~[Bi]
    def of[Bi[_[_], _[_]]]: MkForallKBi[Bi]
    def mk[X](implicit u: Unapply[X]): MkForallKBi[u.Bi] = of[u.Bi]

    sealed trait MkForallKBi[Bi[_[_], _[_]]] extends Any {
      type T[_]
      type U[_]
      def from(ft: Bi[T, U]): ∀~∀~[Bi]
      def apply(ft: Bi[T, U]): ∀~∀~[Bi] = from(ft)
    }

    trait Unapply[X] { type Bi[_[_], _[_]] }
    object Unapply {
      implicit def unapply[Ci[_[_], _[_]]]: Unapply[∀~∀~[Ci]] { type Bi[F[_], G[_]] = Ci[F, G] } = new Unapply[∀~∀~[Ci]] { type Bi[F[_], G[_]] = Ci[F, G] }
    }
  }

  private[exo] object ForallKKImpl extends ForallKKModule {
    type Any1[x] = Any
    type ForallKBi[Bi[_[_], _[_]]] = Bi[Any1, Any1]

    def specialize[Bi[_[_], _[_]], F[_], G[_]](f: ∀~∀~[Bi]): Bi[F, G] = f.asInstanceOf[Bi[F, G]]
    def from[Bi[_[_], _[_]]](p: Prototype[Bi]): ∀~∀~[Bi] = p[Any, Any]
    def of[Bi[_[_], _[_]]]: MkForallKBi[Bi] = new MkForallKKImpl[Bi]
  }


  object ForallModule {
    implicit final class Ops[F[_]](val f: ∀[F]) {
      def of[A]: F[A]    = Forall.specialize(f)
      def apply[A]: F[A] = of[A]
      def lift[G[_]]: ∀[λ[X => F[G[X]]]] = ∀.of[λ[ᵒ => F[G[ᵒ]]]](of)
      def const[A](a: A): ∀[λ[X => A]] = ∀.of[λ[X => A]].apply(a)
    }

    implicit class NaturalTransformationOps[F[_], G[_]](val trans: F ~> G) {
      def $(f: ∀[F]): ∀[G] = ∀.of[G](trans.exec(f.apply))
      def exec[A](fa: F[A]): G[A] = trans[A](fa)
      def andThen[H[_]](fn2: G ~> H): F ~> H = ∀.mk[F ~> H].from(trans.apply.andThen(fn2.apply))
      def andThen_[H[_], I[_]](fn2: H ~> I)(implicit eq: G =~= H): F ~> I = eq.subst(trans).andThen(fn2)
    }

    // https://nokyotsu.com/qscripts/2014/07/distribution-of-quantifiers-over-logic-connectives.html
    //////////////////////////// ⨂
    /** ∀ distributes over Tuple2 */
    def fnPdTo[F[_], G[_]]: ∀[λ[x => (F[x], G[x])]] => (∀[F], ∀[G]) =
      f => (∀.of[F].fromH(t => f.apply[t.T]._1), ∀.of[G].fromH(t => f.apply[t.T]._2))
    def fnPdFr[F[_], G[_]]: ((∀[F], ∀[G])) => ∀[λ[x => (F[x], G[x])]] =
      {case (f, g) => ∀.of[λ[x => (F[x], G[x])]].fromH(t => (f[t.T], g[t.T]))}
    def isoDistribTuple[F[_], G[_]]: ∀[λ[x => (F[x], G[x])]] <=> (∀[F], ∀[G]) = Iso.unsafe(fnPdTo, fnPdFr)

    //////////////////////// ⨁
    /** ∀ distributes over \/ (one way only) */
    def fnCdFr[F[_], G[_]]: (∀[F] \/ ∀[G]) => ∀[λ[x => F[x] \/ G[x]]] =
      e => ∀.of[λ[x => F[x] \/ G[x]]].fromH(t => e.fold(_.apply[t.T].left, _.apply[t.T].right))

    ////////////////////////
    /** ∀ kinda distributes over => */
    def fnDistTo[A, F[_]]: ∀[λ[x => A => F[x]]] => A => ∀[F] =
      faf => a => ∀.of[F](faf.apply.apply(a))
    def fnDistFrom[A, F[_]]: (A => ∀[F]) => ∀[λ[x => A => F[x]]] =
      afa => ∀.of[λ[x => A => F[x]]](a => afa(a).apply)
    def isoDistribFn[A, F[_]]: ∀[λ[x => A => F[x]]] <=> (A => ∀[F]) = Iso.unsafe(fnDistTo, fnDistFrom)

    ////////////////////////
    /** ∀ is commutative */
    def commute1[F[_,_]]: ∀[λ[a => ∀[F[a, *]]]] => ∀[λ[b => ∀[F[*, b]]]] =
      ab => ∀.of[λ[b => ∀[F[*, b]]]].fromH(b => ∀.of[F[*, b.T]].fromH(a => ab[a.T][b.T]))
    def commute2[F[_,_]]: ∀[λ[b => ∀[F[*, b]]]] => ∀[λ[a => ∀[F[a, *]]]] =
      ab => ∀.of[λ[a => ∀[F[a, *]]]].fromH(a => ∀.of[F[a.T, *]].fromH(b => ab[b.T][a.T]))
    def isoCommute[F[_,_]]: ∀[λ[a => ∀[λ[b => F[a, b]]]]] <=> ∀[λ[b => ∀[λ[a => F[a, b]]]]] =
      Iso.unsafe(commute1[F], commute2[F])

    ////////////////////////
  }
  object Forall2Module {
    implicit final class Ops[F[_, _]](val a: ∀∀[F]) extends AnyVal {
      def of   [A, B]: F[A, B] = Forall2.specialize(a)
      def apply[A, B]: F[A, B] = of[A, B]
    }

    implicit class BinaturalTransformationOps[F[_, _], G[_, _]](val trans: F ~~> G) extends AnyVal {
      def $(f: ∀∀[F]): ∀∀[G] = ∀∀.of[G](trans.apply.apply(f.apply))
      def exec[A, B](fa: F[A, B]): G[A, B] = trans[A, B](fa)
      def andThen[H[_,_]](fn2: G ~~> H): F ~~> H = ∀∀.mk[F ~~> H].from(trans.apply.andThen(fn2.apply))
      def andThen_[H[_,_], I[_,_]](fn2: H ~~> I)(implicit eq: G =~~= H): F ~~> I = eq.subst(trans).andThen(fn2)
    }
  }
  object Forall3Module {
    implicit final class Ops[F[_,_,_]](val a: ∀∀∀[F]) extends AnyVal {
      def of   [A, B, C]: F[A, B, C] = Forall3.specialize(a)
      def apply[A, B, C]: F[A, B, C] = of[A, B, C]
    }
  }
  object ForallKModule {
    implicit final class Ops[Alg[_[_]]](val a: ∀~[Alg]) {
      def of   [F[_]]: Alg[F] = ForallK.specialize(a)
      def apply[F[_]]: Alg[F] = of[F]
    }
  }
  object ForallK1Module {
    implicit final class Ops[Alg[_[_],_]](val a: ForallK1[Alg]) {
      def of   [F[_], X]: Alg[F, X] = ForallK1.specialize(a)
      def apply[F[_], X]: Alg[F, X] = of[F, X]
    }
  }
  object ForallK2Module {
    implicit final class Ops[Bi[_[_,_]]](val a: ∀∀~[Bi]) {
      def of   [F[_,_]]: Bi[F] = ForallK2.specialize(a)
      def apply[F[_,_]]: Bi[F] = of[F]
    }
  }
  object ForallK11Module {
    implicit final class Ops[Alg[_[_],_,_]](val a: ForallK11[Alg]) {
      def of   [F[_], X, Y]: Alg[F, X, Y] = ForallK11.specialize(a)
      def apply[F[_], X, Y]: Alg[F, X, Y] = of[F, X, Y]
    }
  }
  object ForallKKModule {
    implicit final class Ops[Bi[_[_], _[_]]](val a: ∀~∀~[Bi]) {
      def of   [F[_], G[_]]: Bi[F, G] = ForallKBi.specialize(a)
      def apply[F[_], G[_]]: Bi[F, G] = of[F, G]
    }
  }
  object ForallHKModule {
    implicit final class Ops[Alg[_[_[_]]]](val a: ForallHK[Alg]) {
      def of   [F[_[_]]]: Alg[F] = ForallHK.specialize(a)
      def apply[F[_[_]]]: Alg[F] = of[F]
    }
  }

  private[exo] final class MkForallImpl[F[_]](val dummy: Boolean = false) extends AnyVal with ForallImpl.MkForall[F] {
    type T = Any
    def from(ft: F[T]): ForallImpl.∀[F] = ft
  }
  private[exo] final class MkForall2Impl[F[_,_]](val dummy: Boolean = false) extends AnyVal with Forall2Impl.MkForall2[F] {
    type T = Any
    type U = Any
    def from(ft: F[T, U]): Forall2Impl.∀∀[F] = ft
  }
  private[exo] final class MkForall3Impl[F[_,_,_]](val dummy: Boolean = false) extends AnyVal with Forall3Impl.MkForall3[F] {
    type A = Any
    type B = Any
    type C = Any
    def from(ft: F[A, B, C]): Forall3Impl.∀∀∀[F] = ft
  }
  private[exo] final class MkForallKImpl[Alg[_[_]]](val dummy: Boolean = false) extends AnyVal with ForallKImpl.MkForallK[Alg] {
    type T[α] = Any
    def from(ft: Alg[T]): ForallKImpl.∀~[Alg] = ft
  }
  private[exo] final class MkForallHKImpl[Alg[_[_[_]]]](val dummy: Boolean = false) extends AnyVal with ForallHKImpl.MkForallHK[Alg] {
    type T[α[_]] = Any
    def from(ft: Alg[T]): ForallHKImpl.ForallHK[Alg] = ft
  }
  private[exo] final class MkForallK1Impl[Alg[_[_],_]](val dummy: Boolean = false) extends AnyVal with ForallK1Impl.MkForallK1[Alg] {
    type T[α] = α => Any
    type X = Any
    def from(ft: Alg[T,X]): ForallK1Impl.ForallK1[Alg] = ft
  }
  private[exo] final class MkForallK2Impl[Bi[_[_,_]]](val dummy: Boolean = false) extends AnyVal with ForallK2Impl.MkForallK2[Bi] {
    type T[a,b] = Any
    def from(ft: Bi[T]): ForallK2Impl.∀∀~[Bi] = ft
  }
  private[exo] final class MkForallK11Impl[Alg[_[_],_,_]](val dummy: Boolean = false) extends AnyVal with ForallK11Impl.MkForallK11[Alg] {
    type T[α] = α => Any
    type X = Any
    type Y = Any
    def from(ft: Alg[T,X,Y]): ForallK11Impl.ForallK11[Alg] = ft
  }
  private[exo] final class MkForallKKImpl[Bi[_[_], _[_]]](val dummy: Boolean = false) extends AnyVal with ForallKKImpl.MkForallKBi[Bi] {
    type T[_] = Any
    type U[_] = Any
    def from(ft: Bi[T, U]): ForallKKImpl.∀~∀~[Bi] = ft
  }

}
