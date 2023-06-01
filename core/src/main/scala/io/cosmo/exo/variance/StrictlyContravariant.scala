package io.cosmo.exo.variance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.inhabitance.*

sealed abstract class StrictlyContravariant[F[_]] { F =>
  def apply[A, B](using ab: A </< B): F[B] </< F[A]

  val injective: IsInjective[F] = new IsInjective[F] {
    override def apply[X, Y](using ev: F[X] === F[Y]): X === Y =
      Parametric[F].lowerInj[Void, Any, X, Y](F[Void, Any](using StrictAs.bottomTop).inequality[F[Any], F[Void]].flip, ev)
  }

  val contravariant: IsContravariant[F] = new IsContravariant[F] {
    override def apply[A, B](using ab: A <~< B): F[B] <~< F[A] =
      Inhabited.lem[A === B].map {
        _.fold(nab => F(using StrictAs.witness(WeakApart.witness(nab), ab)).conformity, ab => ab.lift[F].flip.toAs)
      }.proved
  }

  def substCo[G[+_], A, B](g: G[F[B]])(using ev: A <~< B): G[F[A]] = contravariant.substCo[G, A, B](g)

  def substCt[G[-_], A, B](g: G[F[A]])(using ev: A <~< B): G[F[B]] = contravariant.substCt[G, A, B](g)

  def lift[A, B](ab: A <~< B): F[B] <~< F[A] = contravariant(using ab)

  def liftStrict[A, B](ab: StrictAs[A, B]): StrictAs[F[B], F[A]] =
    StrictAs.witness[F[B], F[A]](using
      injective.contrapositive(ab.inequality.flip),
      contravariant(using ab.conformity)
    )

  def composeCo[G[_]](G: StrictlyCovariant[G]): StrictlyContravariant[[x] =>> F[G[x]]] =
    StrictlyContravariant.witness[[x] =>> F[G[x]]](using
      injective.compose[G](G.injective),
      contravariant.composeCo[G](G.covariant)
    )

  def composeCt[G[_]](G: StrictlyContravariant[G]): StrictlyCovariant[[x] =>> F[G[x]]] =
    StrictlyCovariant.witness[[x] =>> F[G[x]]](using
      injective.compose[G](G.injective),
      contravariant.composeCt[G](G.contravariant)
    )

  def composeCoNS[G[_]](G: IsCovariant[G]): IsContravariant[[x] =>> F[G[x]]] = contravariant.composeCo[G](G)

  def composeCtNS[G[_]](G: IsContravariant[G]): IsCovariant[[x] =>> F[G[x]]] = contravariant.composeCt[G](G)

  def composePh[G[_]](G: IsConstant[G]): IsConstant[[x] =>> F[G[x]]] = contravariant.composePh[G](G)
}
object StrictlyContravariant {
  def apply[F[_]](using F: StrictlyContravariant[F]): StrictlyContravariant[F] = F

  given witness[F[_]](using I: IsInjective[F], C: IsContravariant[F]): StrictlyContravariant[F] = new StrictlyContravariant[F] {
    override def apply[A, B](using ab: A </< B): F[B] </< F[A] =
      StrictAs.witness[F[B], F[A]](
        WeakApart.witness(fab => ab.inequality.run(I(fab).flip)),
        C[A, B](using ab.conformity))
  }

  given proposition[F[_]]: Proposition[StrictlyContravariant[F]] =
    Proposition.witness((A: ¬¬[StrictlyContravariant[F]]) => new StrictlyContravariant[F] {
      override def apply[A, B](using ab: A </< B): F[B] </< F[A] = A.map(_[A, B]).proved
    })
}
