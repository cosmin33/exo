package io.cosmo.exo.variance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.inhabitance.*

trait IsConstant[F[_]] { F =>
  def apply[A, B]: F[A] === F[B]

  /**
   * Constant type constructors are not injective.
   */
  def notInjective(injF: IsInjective[F]): Void =
    injF(using F[Unit, Void]).coerce(())

  def subst[G[_], A, B](g: G[F[A]]): G[F[B]] =
    F[A, B].subst[G](g)

  def compose[G[_]]: IsConstant[[x] =>> F[G[x]]] =
    IsConstant.witness[[x] =>> F[G[x]]](using F[G[Void], G[Any]])

  def andThenCo[G[_]](using G: IsCovariant[G]): IsConstant[[x] =>> G[F[x]]] =
    IsConstant.witness[[x] =>> G[F[x]]](using As.bracket(G(using F[Void, Any].toAs), G(using F[Any, Void].toAs)))

  def andThenCt[G[_]](using G: IsContravariant[G]): IsConstant[[x] =>> G[F[x]]] =
    IsConstant.witness[[x] =>> G[F[x]]](using As.bracket(G(using F[Any, Void].toAs), G(using F[Void, Any].toAs)))

  def asCovariant: IsCovariant[F] =
    IsCovariant.witness[F](using F[Void, Any].toAs)

  def asContravariant: IsContravariant[F] =
    IsContravariant.witness[F](using F[Any, Void].toAs)
}

object IsConstant {
  def apply[F[_]](using ev: IsConstant[F]): IsConstant[F] = ev

  type Canonic[F[_]] = ∀∀[[a,b] =>> F[a] === F[b]]

  def isoCanonic[F[_]]: Canonic[F] <=> IsConstant[F] =
    Iso.unsafe(
      c => witness(using c.apply[Void, Any]),
      i => ∀∀.mk[Canonic[F]].from(i.apply)
    )

  def witness[F[_]](using fab: F[Void] === F[Any]): IsConstant[F] =
    witness1[F, Void, Any](Void.isNotAny, fab)

  def witness1[F[_], A, B](nab: A =!= B, fab: F[A] === F[B]): IsConstant[F] =
    new IsConstant[F]:
      def apply[X, Y]: F[X] === F[Y] = Parametric[F].liftPh[A, B, X, Y](nab, fab)

  given const[A]: IsConstant[[x] =>> A] = witness[[x] =>> A](using Is.refl[A])

  def bracket[F[_]](cvF: IsCovariant[F], ctF: IsContravariant[F]): IsConstant[F] = {
    val p :   Void  <~<   Any  = As.bottomTop
    val s : F[Void] === F[Any] = Axioms.bracket(cvF(using p), ctF(using p))
    witness[F](using s)
  }

  given proposition[F[_]]: Proposition[IsConstant[F]] =
    Proposition.witness((A: ¬¬[IsConstant[F]]) => new IsConstant[F] {
      override def apply[A, B]: F[A] === F[B] = A.map(_[A, B]).proved
    })
}
