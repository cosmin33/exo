package io.cosmo.exo.variance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.inhabitance.*

trait StrictlyCovariant[F[_]] { F =>
  def apply[A, B](using ab: A </< B): F[A] </< F[B]

  val injective: IsInjective[F] = new IsInjective[F] {
    override def apply[X, Y](using ev: F[X] === F[Y]): X === Y =
      Parametric[F].lowerInj(F[Void, Any](using StrictAs.bottomTop).inequality[F[Void], F[Any]], ev)
  }

  val covariant: IsCovariant[F] = new IsCovariant[F] {
    override def apply[A, B](using ab: A <~< B): F[A] <~< F[B] =
      Inhabited.lem[A === B].map {
        _.fold(
          nab => F(using StrictAs.witness(WeakApart.witness(nab), ab)).conformity,
          ab => ab.lift[F].toAs
        )
      }.proved
  }

  def substCo[G[+_], A, B](g: G[F[A]])(using ev: A <~< B): G[F[B]] = covariant.substCo[G, A, B](g)

  def substCt[G[-_], A, B](g: G[F[B]])(using ev: A <~< B): G[F[A]] = covariant.substCt[G, A, B](g)

  def liftStrict[A, B](ab: StrictAs[A, B]): StrictAs[F[A], F[B]] =
    StrictAs.witness[F[A], F[B]](
      injective.contrapositive(ab.inequality),
      covariant(using ab.conformity))

  def composeCo[G[_]](G: StrictlyCovariant[G]): StrictlyCovariant[[x] =>> F[G[x]]] =
    StrictlyCovariant.witness[[x] =>> F[G[x]]](using
      injective.compose[G](G.injective),
      covariant.composeCo[G](G.covariant)
    )

  def composeCt[G[_]](G: StrictlyContravariant[G]): StrictlyContravariant[[x] =>> F[G[x]]] =
    StrictlyContravariant.witness[[x] =>> F[G[x]]](using
      injective.compose[G](G.injective),
      covariant.composeCt[G](G.contravariant)
    )

  def composeCoNS[G[_]](G: IsCovariant[G]): IsCovariant[[x] =>> F[G[x]]] = covariant.composeCo[G](G)

  def composeCtNS[G[_]](G: IsContravariant[G]): IsContravariant[[x] =>> F[G[x]]] = covariant.composeCt[G](G)

  def composePh[G[_]](G: IsConstant[G]): IsConstant[[x] =>> F[G[x]]] = covariant.composePh[G](G)
}
object StrictlyCovariant {
  def apply[F[_]](using F: StrictlyCovariant[F]): StrictlyCovariant[F] = F

  given witness[F[_]](using I: IsInjective[F], C: IsCovariant[F]): StrictlyCovariant[F] = new StrictlyCovariant[F] {
    override def apply[A, B](using ab: A </< B): F[A] </< F[B] =
      StrictAs.witness[F[A], F[B]](
        WeakApart.witness(fab => ab.inequality.run(I(fab))),
        C[A, B](using ab.conformity))
  }

  given proposition[F[_]]: Proposition[StrictlyCovariant[F]] =
    Proposition.witness((A: ¬¬[StrictlyCovariant[F]]) => new StrictlyCovariant[F] {
      override def apply[A, B](using ab: A </< B): F[A] </< F[B] = A.map(_[A, B]).proved
    })
}
