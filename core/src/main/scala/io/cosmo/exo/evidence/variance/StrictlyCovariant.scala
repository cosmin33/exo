package io.cosmo.exo.evidence.variance

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.evidence._

trait StrictlyCovariant[F[_]] { F =>
  import StrictlyCovariant._

  def apply[A, B](implicit ab: A </< B): F[A] </< F[B]

  val injective: IsInjective[F] = new IsInjective[F] {
    override def apply[X, Y](implicit ev: F[X] === F[Y]): X === Y =
      Parametric[F].lowerInj(F[Void, Any](StrictAs.bottomTop).inequality[F[Void], F[Any]], ev)
  }

  val covariant: IsCovariant[F] = new IsCovariant[F] {
    override def apply[A, B](implicit ab: A <~< B): F[A] <~< F[B] =
      Inhabited.lem[A === B].map {
        _.fold(
          nab => F(StrictAs.witness(WeakApart.witness(nab.run), ab)).conformity,
          ab => ab.lift[F].toAs
        )
      }.proved
//      Inhabited.lem[A === B].map {
//        case \/-(ab) => ab.lift[F].toAs
//        case -\/(nab) => F(StrictAs.witness(WeakApart.witness(nab.run), ab)).conformity
//      }.proved
  }

  def substCo[G[+_], A, B](g: G[F[A]])(implicit ev: A <~< B): G[F[B]] =
    covariant.substCo[G, A, B](g)

  def substCt[G[-_], A, B](g: G[F[B]])(implicit ev: A <~< B): G[F[A]] =
    covariant.substCt[G, A, B](g)

  def liftStrict[A, B](ab: StrictAs[A, B]): StrictAs[F[A], F[B]] =
    StrictAs.witness[F[A], F[B]](
      injective.contrapositive(ab.inequality),
      covariant(ab.conformity))

  def composeCo[G[_]](G: StrictlyCovariant[G]): StrictlyCovariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](
      injective.compose[G](G.injective),
      covariant.composeCo[G](G.covariant))

  def composeCt[G[_]](G: StrictlyContravariant[G]): StrictlyContravariant[λ[x => F[G[x]]]] =
    StrictlyContravariant.witness[λ[x => F[G[x]]]](
      injective.compose[G](G.injective),
      covariant.composeCt[G](G.contravariant))

  def composeCoNS[G[_]](G: IsCovariant[G]): IsCovariant[λ[x => F[G[x]]]] =
    covariant.composeCo[G](G)

  def composeCtNS[G[_]](G: IsContravariant[G]): IsContravariant[λ[x => F[G[x]]]] =
    covariant.composeCt[G](G)

  def composePh[G[_]](G: IsConstant[G]): IsConstant[λ[x => F[G[x]]]] =
    covariant.composePh[G](G)
}
object StrictlyCovariant {
  def apply[F[_]](implicit F: StrictlyCovariant[F]): StrictlyCovariant[F] = F

  implicit def witness[F[_]](implicit I: IsInjective[F], C: IsCovariant[F]): StrictlyCovariant[F] = new StrictlyCovariant[F] {
    override def apply[A, B](implicit ab: A </< B): F[A] </< F[B] =
      StrictAs.witness[F[A], F[B]](
        WeakApart.witness(fab => ab.inequality(I(fab))),
        C[A, B](ab.conformity))
  }

  implicit def proposition[F[_]]: Proposition[StrictlyCovariant[F]] =
    (A: ¬¬[StrictlyCovariant[F]]) => new StrictlyCovariant[F] {
      override def apply[A, B](implicit ab: A </< B): F[A] </< F[B] = A.map(_[A, B]).proved
    }
}
