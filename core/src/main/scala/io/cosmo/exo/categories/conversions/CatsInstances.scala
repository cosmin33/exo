package io.cosmo.exo.categories.conversions

import cats.{~> => _, _}
import cats.arrow.{Category, Compose, FunctionK}
import cats.data.OptionT
import io.cosmo.exo._
import io.cosmo.exo.categories.conversions.CatsInstancesTraits._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.categories.{Semicategory, Subcat, Trivial}
import shapeless.LowPriority

object CatsInstances extends CatsInstances01 {
  implicit def semi2comp[->[_,_]](implicit lp: LowPriority, s: Semicategory[->]): Compose[->] = new ComposeFromSemicat[->] { val S = s }
  implicit def comp2semi[->[_,_]](implicit c: Compose[->]): Semicategory[->] = new SemicatFromCompose[->] { val C = c }

  implicit def exo2cov[F[_]](implicit lp: LowPriority, F: Endofunctor.CovF[F]): Functor[F] = Exofunctor.isoCatsCovariant[F].to(F)
  implicit def cov2exo[F[_]](implicit F: Functor[F]): Endofunctor.CovF[F] = Exofunctor.isoCatsCovariant[F].from(F)

  implicit def exo2con[F[_]](implicit lp: LowPriority, F: Exofunctor.ConF[F]): Contravariant[F] = Exofunctor.isoCatsContravariant[F].to(F)
  implicit def con2exo[F[_]](implicit F: Contravariant[F]): Exofunctor.ConF[F] = Exofunctor.isoCatsContravariant[F].from(F)

  implicit def optionTFunctorK[A]: FunctorK[OptionT[*[_], A]] =
    new FunctorK.Proto[OptionT[*[_], A]] {
      def mapK[F[_], G[_]](f: F ~> G): OptionT[F, A] => OptionT[G, A] = o => OptionT[G, A](f.apply[Option[A]](o.value))
    }

  implicit def functorFunctorK: IsoFunctorK[Functor] =
    new IsoFunctorK.Proto[Functor] {
      def mapK[F[_], G[_]](iso: F <~> G): Functor[F] => Functor[G] =
        ff => new Functor[G] {
          def map[A, B](fa: G[A])(f: A => B): G[B] = iso.apply[B].to(ff.map(iso.apply[A].from(fa))(f))
        }
    }

}

trait CatsInstances01 {
  implicit def sub2cat[->[_,_]](implicit lp: LowPriority, s: Subcat.Aux[->, Trivial.T1]): Category[->] = new CategoryFromSubcat[->] { val S = s }
  implicit def cat2sub[->[_,_]](implicit lp: LowPriority, c: Category[->]): Subcat.Aux[->, Trivial.T1] = new SubcatFromCategory[->] { val C = c }

  implicit def inv2exo[F[_]](implicit lp: LowPriority, F: Exofunctor.InvF[F]): Invariant[F] = Exofunctor.isoCatsInvariant[F].to(F)
  implicit def exo2inv[F[_]](implicit F: Invariant[F]): Exofunctor.InvF[F] = Exofunctor.isoCatsInvariant[F].from(F)
}

object CatsInstancesHelpers {
}

object CatsInstancesTraits {
  trait ComposeFromSemicat[->[_,_]] extends Compose[->] {
    protected def S: Semicategory[->]
    def compose[A, B, C](f: B -> C, g: A -> B) = S.compose(f, g)
  }
  trait CategoryFromSubcat[->[_,_]] extends Category[->] with ComposeFromSemicat[->] {
    protected def S: Subcat.Aux[->, Trivial.T1]
    def id[A] = S.id[A]
  }

  trait SemicatFromCompose[->[_,_]] extends Semicategory[->] {
    protected def C: Compose[->]
    def andThen[A, B, C](ab: A -> B, bc: B -> C) = C.andThen(ab, bc)
  }
  trait SubcatFromCategory[->[_,_]] extends Subcat[->] with SemicatFromCompose[->] {
    protected def C: Category[->]
    type TC[x] = Trivial.T1[x]
    def id[A](implicit A: Trivial.T1[A]) = C.id[A]
  }
}