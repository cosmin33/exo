package io.cosmo.exo.categories.functors

import cats.arrow.Category
import cats.data.{Cokleisli, Kleisli}
import cats.implicits._
import cats.{CoflatMap, Contravariant, FlatMap, Functor, FunctorFilter, Invariant, Monad, Traverse, TraverseFilter}
import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.conversions.CatsInstances
import io.cosmo.exo.categories.conversions.CatsInstances._
import io.cosmo.exo.evidence.TypeHolder2
import io.cosmo.exo.typeclasses.HasTc
import mouse.any._
import shapeless.the

trait Exofunctor[==>[_,_], -->[_,_], F[_]] {
  def C : Semicategory[==>]
  def D : Semicategory[-->]
  def map[A, B](f: A ==> B): F[A] --> F[B]
}

object Exofunctor extends ExofunctorImplicits {

  type Cov[->[_,_], F[_]] = Exofunctor[->, * => *, F]
  /** This is isomorphic with cats.Functor */
  type CovF[F[_]] = Cov[* => *, F]

  type Con[->[_,_], F[_]] = Exofunctor[Dual[->,*,*], * => *, F]
  /** This is isomorphic with cats.Contravariant */
  type ConF[F[_]] = Con[* => *, F]

  type Inv[->[_,_], F[_]] = Exofunctor[Dicat[->,*,*], * => *, F]
  /** This is isomorphic with cats.Invariant */
  type InvF[F[_]] = Inv[* => *, F]

  /** Exofunctor from an isomorphism category to Function1 */
  type IsoFun[->[_,_], F[_]] = Exofunctor[Iso[->,*,*], * => *, F]

  /** Exofunctor from Function to an isomorphism category */
  type FunIso[->[_,_], F[_]] = Exofunctor[* => *, Iso[->,*,*], F]

  /** Map on (A <-> B) gives you typeclass derivation: {{{HasTc[TC, A] => HasTc[TC, B]}}} */
  type IsoTypeclass[->[_,_], TC[_[_]]] = IsoFun[->, HasTc[TC, *]]

//  case class SingleOf[T, U <: {type TC1[_]; type TC2[_]}](widen: T {type TC1[a] = U#TC1[a]; type TC2[a] = U#TC2[a]})
//  object SingleOf {
//    implicit def mkSingleOf[T <: {type TC1[_]; type TC2[_]}](implicit t: T): SingleOf[T, t.type] = SingleOf(t)
//  }

  def unsafe[==>[_,_], -->[_,_], F[_]]: MkExofunctor[==>, -->, F] = new MkExofunctor[==>, -->, F]()

  final class MkExofunctor[==>[_,_], -->[_,_], F[_]](val b: Boolean = true) extends AnyVal {
    type X
    type Y
    def apply(fn: (X ==> Y) => (F[X] --> F[Y]))(implicit
      c1: Semicategory[==>],
      c2: Semicategory[-->],
    ) = new Exofunctor[==>, -->, F] {
      val C = c1
      val D = c2
      def map[A, B](f: A ==> B): F[A] --> F[B] = fn.asInstanceOf[(A ==> B) => (F[A] --> F[B])](f)
    }
    def applyH(f: TypeHolder2[X, Y] => (X ==> Y) => F[X] --> F[Y])(implicit
      c1: Semicategory[==>],
      c2: Semicategory[-->],
    ): Exofunctor[==>, -->, F] = apply(f(TypeHolder2[X, Y]))
  }

  implicit def catsIsoContravariant[F[_]]: Exofunctor.ConF[F] <=> Contravariant[F] =
    Iso.unsafe(
      F => new Contravariant[F] {def contramap[A, B](fa: F[A])(f: B => A): F[B] = F.map[A, B](Dual(f))(fa)},
      F => Exo.unsafe[Dual[* => *,*,*], * => *, F](ba => F.contramap(_)(ba))
    )

  implicit def catsIsoInvariant[F[_]]: Exofunctor.InvF[F] <=> Invariant[F] =
    Iso.unsafe(
      F => new Invariant[F] {def imap[A, B](fa: F[A])(f: A => B)(g: B => A): F[B] = F.map((f, Dual(g)))(fa)},
      I => Exo.unsafe[Dicat[* => *, *, *], * => *, F].apply(f => I.imap(_)(f._1)(f._2))
    )

  implicit def catsIsoCovariant[F[_]]: Endofunctor.CovF[F] <=> Functor[F] =
    Iso.unsafe(
      F => new Functor[F] { def map[A, B](fa: F[A])(f: A => B): F[B] = F.map[A, B](f)(fa) },
      F => Exo.unsafe[* => *, * => *, F](ab => F.map(_)(ab))
    )

  implicit def exoFromCatsTraverse[M[_]: Monad, F[_]: Traverse]: Endofunctor[Kleisli[M,*,*], F] =
    new Endofunctor[Kleisli[M,*,*], F] {
      val C, D = CatsInstances.comp2semi[Kleisli[M, *, *]]
      def map[A, B](f: Kleisli[M, A, B]): Kleisli[M, F[A], F[B]] = Kleisli(_.traverse(f.run))
    }
  def exoFromTraverse1[M[_]: Monad, F[_]: Traverse]: Endofunctor[λ[(a,b) => a => M[b]], F] =
    new Endofunctor[λ[(a,b) => a => M[b]], F] {
      val C, D = new Semicategory[λ[(a,b) => a => M[b]]] {
        def andThen[A, B, C](ab: A => M[B], bc: B => M[C]): A => M[C] = ab(_).flatMap(bc)
      }
      def map[A, B](f: A => M[B]): F[A] => M[F[B]] = _.traverse(f)
    }

  def isoCatsFunctorFilter[F[_]]: FunctorFilter[F] <=> Exofunctor[λ[(a,b) => a => Option[b]], * => *, F] = ???

  def isoCatsTravFilter[F[_], M[_]: Monad]
  : TraverseFilter[F] <=> Exofunctor[λ[(a,b) => a => M[Option[b]]], λ[(a,b) => a => M[b]], F] = ???

  implicit def exoFromCatsFlatMap[F[_]: FlatMap]: Exofunctor[Kleisli[F,*,*], * => *, F] =
      new Exofunctor[Kleisli[F,*,*], * => *, F] {
        def C = CatsInstances.comp2semi[Kleisli[F, *, *]]
        def D = Semicategory.function1
        def map[A, B](f: Kleisli[F, A, B]): F[A] => F[B] = _.flatMap(f.run)
      }
  def exoFromFlatMap1[F[_]: FlatMap]: Exofunctor[λ[(a,b) => a => F[b]], * => *, F] =
      new Exofunctor[λ[(a,b) => a => F[b]], * => *, F] {
        def C = new Semicategory[λ[(a,b) => a => F[b]]] {
          def andThen[A, B, C](ab: A => F[B], bc: B => F[C]): A => F[C] = ab(_).flatMap(bc)
        }
        def D = Semicategory.function1
        def map[A, B](f: A => F[B]): F[A] => F[B] = _.flatMap(f)
      }

  implicit def exoFromCatsCoflatMap[F[_]: CoflatMap]: Exofunctor[Cokleisli[F,*,*], * => *, F] =
    new Exofunctor[Cokleisli[F,*,*], * => *, F] {
      def C = CatsInstances.comp2semi[Cokleisli[F, *, *]]
      def D = Semicategory.function1
      def map[A, B](f: Cokleisli[F, A, B]): F[A] => F[B] = _.coflatMap(f.run)
    }
  def exoFromCoflatMap1[F[_]: CoflatMap]: Exofunctor[λ[(a,b) => F[a] => b], * => *, F] =
    new Exofunctor[λ[(a,b) => F[a] => b], * => *, F] {
      def C = new Semicategory[λ[(a,b) => F[a] => b]] {
        def andThen[A, B, C](ab: F[A] => B, bc: F[B] => C): F[A] => C = _.coflatMap(ab) |> bc
      }
      def D = Semicategory.function1
      def map[A, B](f: F[A] => B): F[A] => F[B] = _.coflatMap(f)
    }

}

trait ExofunctorImplicits extends ExofunctorImplicits01 {
//  implicit def blah1[->[_,_], F[_]](implicit
//    e: Exo.Inv[->, F]
//  ): Exo.IsoFun[->, F] = //Exo.unsafe[Iso[->,*,*], * => *, F](i => e.map((i.to, Dual(i.from))))
//    new Exo.IsoFun[->, F] {
//      def C = ???
//      def D = ???
//      implicitly[Subcat[Iso[* => *, *, *]]]
//      def map[A, B](f: Iso[->, A, B]) = e.map((f.to, Dual(f.from)))
//    }
  implicit def covToInv[->[_,_], F[_]](implicit e: Exo.Cov[->, F]): Exo.Inv[->, F] =
    new Exo.Inv[->, F] {
      def C: Semicategory[Dicat[->, *, *]] = prodcatSemicat(e.C, Semicategory.dualSemicategory(e.C))
      def D: Semicategory[Function] = implicitly
      def map[A, B](f: (A -> B, Dual[->, A, B])) = e.map(f._1)
    }
}

trait ExofunctorImplicits01 {
//  implicit def conToInv[->[_,_], F[_]](implicit e: Exo.Con[->, F]): Exo.Inv[->, F] =
//    new Exo.Inv[->, F] {
//      def C: Semicategory[Dicat[->, *, *]] = prodcatSemicat(Semicategory.dualSemicategory(e.C), e.C)
//      def D: Semicategory[Function] = implicitly
//      def map[A, B](f: (A -> B, Dual[->, A, B])) = e.map(f._2)
//    }
}

object Endofunctor {
  /** This is isomorphic with cats.Functor[F] */
  type CovF[F[_]] = Endofunctor[* => *, F]

  def unsafe[->[_,_], F[_]]: Exofunctor.MkExofunctor[->, ->, F] = Exofunctor.unsafe[->, ->, F]

}

//trait Exorepresentable[==>[_,_], ->[_,_], F[_]] {
//  type Representation
//  def functor: Exofunctor[==>, ->, F]
//  def index   [A]: F[A] -> (Representation ==> A)
//  def tabulate[A]: (Representation ==> A) -> F[A]
//
//  private type <->[a,b] = Iso[->,a,b]
//  def iso[A]: (Representation ==> A) <-> F[A] = Iso.unsafe(tabulate[A], index[A])(functor.D)
//}
