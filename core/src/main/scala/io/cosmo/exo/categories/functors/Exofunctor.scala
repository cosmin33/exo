package io.cosmo.exo.categories.functors

import cats.data.{Cokleisli, Kleisli}
import cats.implicits._
import cats.syntax._
import cats.{Applicative, CoflatMap, Contravariant, FlatMap, Functor, FunctorFilter, Invariant, Monad, Traverse, TraverseFilter}
import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.conversions.CatsInstances._
import io.cosmo.exo.evidence.TypeHolder2
import io.cosmo.exo.typeclasses.HasTc

trait Exofunctor[==>[_,_], -->[_,_], F[_]] {
  def map[A, B](f: A ==> B): F[A] --> F[B]

  def compose[G[_]](G: Endofunctor[==>, G]): Exofunctor[==>, -->, λ[α => F[G[α]]]] =
    Exo.unsafe[==>, -->, λ[α => F[G[α]]]](f => map(G.map(f)))

  def composeContra[G[_]](G: Exofunctor[Dual[==>,*,*], ==>, G]): Exofunctor[Dual[==>,*,*], -->, λ[α => F[G[α]]]] =
    Exo.unsafe[Dual[==>,*,*], -->, λ[α => F[G[α]]]](f => map(G.map(f)))

}

object Exofunctor extends ExofunctorImplicits {
  def apply[==>[_,_], -->[_,_], F[_]](implicit E: Exo[==>, -->, F]): Exo[==>, -->, F] = E

  implicit class ExofunctorDualOps[==>[_,_], -->[_,_], F[_]](val F: Exofunctor[Dual[==>,*,*], -->, F]) extends AnyVal {
    def coComposeContra[G[_]](G: Exofunctor[Dual[==>,*,*], ==>, G]): Exofunctor[==>, -->, λ[α => F[G[α]]]] =
      Exo.unsafe[==>, -->, λ[α => F[G[α]]]](f => F.map(Dual(G.map(Dual(f)))))

    def coCompose[G[_]](G: Endofunctor[==>, G]): Exofunctor[Dual[==>,*,*], -->, λ[α => F[G[α]]]] =
      Exo.unsafe[Dual[==>,*,*], -->, λ[α => F[G[α]]]](f => F.map(Dual(G.map(f))))
  }

  type Cov[->[_,_], F[_]] = Exo[->, * => *, F]
  object Cov { def apply[->[_,_], F[_]](implicit E: Cov[->, F]) = E }
  /** This is isomorphic to cats.Functor */
  type CovF[F[_]] = Cov[* => *, F]
  object CovF { def apply[F[_]](implicit E: CovF[F]) = E }

  type Con[->[_,_], F[_]] = Exo[Dual[->,*,*], * => *, F]
  object Con { def apply[->[_,_], F[_]](implicit E: Con[->, F]) = E }
  /** This is isomorphic to cats.Contravariant */
  type ConF[F[_]] = Con[* => *, F]
  object ConF { def apply[F[_]](implicit E: ConF[F]) = E }

  type Inv[->[_,_], F[_]] = Exo[Dicat[->,*,*], * => *, F]
  object Inv { def apply[->[_,_], F[_]](E: Inv[->, F]) = E }
  /** This is isomorphic to cats.Invariant */
  type InvF[F[_]] = Inv[* => *, F]
  object InvF { def apply[F[_]](implicit E: InvF[F]) = E }

  /** Exofunctor from an isomorphism category to Function1 */
  type IsoFun[->[_,_], F[_]] = Exo[Iso[->,*,*], * => *, F]
  object IsoFun { def apply[->[_,_], F[_]](implicit E: IsoFun[->, F]) = E }

  /** Exofunctor from Function to an isomorphism category */
  type FunIso[->[_,_], F[_]] = Exo[* => *, Iso[->,*,*], F]

  /** Map on (A <-> B) gives you typeclass derivation: {{{HasTc[TC, A] => HasTc[TC, B]}}} */
  type IsoTypeclass[TC[_[_]]] = Exo[Iso[FunK,*,*], * => *, HasTc[TC, *]]

  def unsafe[==>[_,_], -->[_,_], F[_]]: MkExofunctor[==>, -->, F] = new MkExofunctor[==>, -->, F]()
  final class MkExofunctor[==>[_,_], -->[_,_], F[_]](val b: Boolean = true) extends AnyVal {
    type X; type Y
    def apply(fn: (X ==> Y) => (F[X] --> F[Y])) = new Exo[==>, -->, F] {
      def map[A, B](f: A ==> B): F[A] --> F[B] = fn.asInstanceOf[(A ==> B) => (F[A] --> F[B])](f)
    }
    def applyH(f: TypeHolder2[X, Y] => (X ==> Y) => F[X] --> F[Y])(implicit
      c1: Semicategory[==>],
      c2: Semicategory[-->],
    ): Exo[==>, -->, F] = apply(f(TypeHolder2[X, Y]))
  }

  implicit def isoCatsContravariant[F[_]]: Exo.ConF[F] <=> Contravariant[F] =
    Iso.unsafe(
      F => new Contravariant[F] {def contramap[A, B](fa: F[A])(f: B => A): F[B] = F.map[A, B](Dual(f))(fa)},
      F => Exo.unsafe[Dual[* => *,*,*], * => *, F](ba => F.contramap(_)(ba))
    )

  implicit def isoCatsInvariant[F[_]]: Exo.InvF[F] <=> Invariant[F] =
    Iso.unsafe(
      F => new Invariant[F] {def imap[A, B](fa: F[A])(f: A => B)(g: B => A): F[B] = F.map((f, Dual(g)))(fa)},
      I => Exo.unsafe[Dicat[* => *, *, *], * => *, F].apply(f => I.imap(_)(f._1)(f._2))
    )

  implicit def isoCatsCovariant[F[_]]: Exo.CovF[F] <=> Functor[F] =
    Iso.unsafe(
      F => new Functor[F] { def map[A, B](fa: F[A])(f: A => B): F[B] = F.map[A, B](f)(fa) },
      F => Exo.unsafe[* => *, * => *, F](ab => F.map(_)(ab))
    )

  implicit def exoFromCatsTraverse[M[_]: Applicative, F[_]: Traverse]: Endofunctor[Kleisli[M,*,*], F] =
    Endofunctor.unsafe[Kleisli[M,*,*], F](f => Kleisli(_.traverse(f.run)))
  implicit def exoFromTraverse1[M[_]: Applicative, F[_]: Traverse]: Endofunctor[λ[(a,b) => a => M[b]], F] =
    Endofunctor.unsafe[λ[(a,b) => a => M[b]], F](f => _.traverse(f))

  implicit def isoCatsFunctorFilter[F[_]]: Exo[λ[(a,b) => a => Option[b]], * => *, F] <=> FunctorFilter[F] =
    Iso.unsafe(
      E => new FunctorFilter[F] {
        def functor = new Functor[F] { def map[A, B](fa: F[A])(f: A => B): F[B] = E.map(f.andThen(_.some))(fa)}
        def mapFilter[A, B](fa: F[A])(f: A => Option[B]) = E.map(f)(fa)
      },
      F => Exo.unsafe[λ[(a,b) => a => Option[b]], * => *, F](f => F.mapFilter(_)(f))
    )

  implicit def exoFromTraverseFilter[F[_]: TraverseFilter, M[_]: Monad]
  : Exo[λ[(a,b) => a => M[Option[b]]], λ[(a,b) => a => M[b]], F] =
    Exo.unsafe[λ[(a,b) => a => M[Option[b]]], λ[(a,b) => a => M[b]], F](f => _.traverseFilter(f))

  implicit def exoFromCatsFlatMap[F[_]: FlatMap]: Exo[Kleisli[F,*,*], * => *, F] =
      Exo.unsafe[Kleisli[F,*,*], * => *, F](f => _.flatMap(f.run))
  implicit def exoFromFlatMap1[F[_]: FlatMap]: Exo[λ[(a,b) => a => F[b]], * => *, F] =
      Exo.unsafe[λ[(a,b) => a => F[b]], * => *, F](f => _.flatMap(f))

  implicit def exoFromCatsCoflatMap[F[_]: CoflatMap]: Exo[Cokleisli[F,*,*], * => *, F] =
    Exo.unsafe[Cokleisli[F,*,*], * => *, F](f => _.coflatMap(f.run))
  implicit def exoFromCoflatMap1[F[_]: CoflatMap]: Exo[λ[(a,b) => F[a] => b], * => *, F] =
    Exo.unsafe[λ[(a,b) => F[a] => b], * => *, F](f => _.coflatMap(f))

}

trait ExofunctorImplicits extends ExofunctorImplicits01 {
  // TODO: generalize these:
  implicit def invToIso[->[_,_], F[_]](implicit e: Exo.Inv[->, F]): Exo.IsoFun[->, F] =
    Exo.unsafe[Iso[->,*,*], * => *, F](i => e.map((i.to, Dual(i.from))))
}

trait ExofunctorImplicits01 extends ExofunctorImplicits02 {
  implicit def covToInv[->[_,_], F[_]](implicit e: Exo.Cov[->, F]): Exo.Inv[->, F] =
    Exo.unsafe[Dicat[->,*,*], * => *, F](f => e.map(f._1))
}

trait ExofunctorImplicits02 {
  implicit def conToInv[->[_,_], F[_]](implicit e: Exo.Con[->, F]): Exo.Inv[->, F] =
    Exo.unsafe[Dicat[->,*,*], * => *, F](f => e.map(f._2))
}

object Endofunctor {
  /** This is isomorphic to cats.Functor[F] */
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
