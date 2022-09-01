package io.cosmo.exo.evidence.variance

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.evidence._

import scala.language.experimental.macros

trait IsConstant[F[_]] { F =>
  import IsConstant._

  def apply[A, B]: F[A] === F[B]

  /**
   * Constant type constructors are not injective.
   */
  def notInjective(injF: IsInjective[F]): Void =
    injF(F[Unit, Void]).coerce(())

  def subst[G[_], A, B](g: G[F[A]]): G[F[B]] =
    F[A, B].subst[G](g)

  def compose[G[_]]: IsConstant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F[G[Void], G[Any]])

  def andThenCo[G[_]](implicit G: IsCovariant[G]): IsConstant[λ[x => G[F[x]]]] =
    witness[λ[x => G[F[x]]]](As.bracket(G(F[Void, Any].toAs), G(F[Any, Void].toAs)))

  def andThenCt[G[_]](implicit G: IsContravariant[G]): IsConstant[λ[x => G[F[x]]]] =
    witness[λ[x => G[F[x]]]](As.bracket(G(F[Any, Void].toAs), G(F[Void, Any].toAs)))

  def asCovariant: IsCovariant[F] =
    IsCovariant.witness[F](F[Void, Any].toAs)

  def asContravariant: IsContravariant[F] =
    IsContravariant.witness[F](F[Any, Void].toAs)
}

trait ConstantLowerPriority {
  implicit def mkConstant[F[_]]: IsConstant[F] =
    macro evidence.internal.MacroUtil.mkConstant[F]
}

object IsConstant extends ConstantLowerPriority {
  type Canonic[F[_]] = ∀∀[λ[(a,b) => F[a] === F[b]]]

  def apply[F[_]](implicit ev: IsConstant[F]): IsConstant[F] = ev

  def isoCanonic[F[_]]: Canonic[F] <=> IsConstant[F] =
    Iso.unsafe(
      c => witness(c.apply[Void, Any]),
      i => ∀∀.mk[Canonic[F]].from(i.apply)
    )

  def witness[F[_]](fab: F[Void] === F[Any]): IsConstant[F] =
    witness1[F, Void, Any](Void.isNotAny, fab)

  def witness1[F[_], A, B](nab: A =!= B, fab: F[A] === F[B]): IsConstant[F] = new IsConstant[F] {
    def apply[X, Y]: F[X] === F[Y] = Parametric[F].liftPh[A, B, X, Y](nab, fab)
  }

  implicit def const[A]: IsConstant[λ[X => A]] =
    witness[λ[X => A]](Is.refl[A])

  def bracket[F[_]](cvF: IsCovariant[F], ctF: IsContravariant[F]): IsConstant[F] = {
    val p :   Void  <~<   Any  = As.bottomTop
    val s : F[Void] === F[Any] = Axioms.bracket(cvF(p), ctF(p))
    witness[F](s)
  }

  implicit def proposition[F[_]]: Proposition[IsConstant[F]] =
    (A: ¬¬[IsConstant[F]]) => new IsConstant[F] {
      override def apply[A, B]: F[A] === F[B] = A.map(_[A, B]).proved
    }
}