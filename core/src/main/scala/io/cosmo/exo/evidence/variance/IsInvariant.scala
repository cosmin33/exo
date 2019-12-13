package io.cosmo.exo.evidence.variance

import cats.implicits._
import io.cosmo.exo.evidence._
import io.cosmo.exo._

trait IsInvariant[F[_]] { F =>
  import IsInvariant._

  def apply[A, B](implicit ev: A =!= B): F[A] >~< F[B]

  def injective: IsInjective[F] =
    IsInjective.witness[F](F(Void.isNotAny).notEqual)

  def composePh[G[_]](G: IsConstant[G]): IsConstant[λ[x => F[G[x]]]] =
    IsConstant.witness[λ[x => F[G[x]]]](G[Void, Any].lift[F])

  def composeInj[G[_]](G: IsInjective[G]): IsInvariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G.contrapositive(Void.isNotAny)))

  def composeStCv[G[_]](G: StrictlyCovariant[G]): IsInvariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G.injective.contrapositive(Void.isNotAny)))

  def composeStCt[G[_]](G: StrictlyContravariant[G]): IsInvariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G.injective.contrapositive(Void.isNotAny)))

  def composeInv [G[_]](G: IsInvariant[G]): IsInvariant[λ[x => F[G[x]]]] =
    witness[λ[x => F[G[x]]]](F(G(Void.isNotAny).notEqual))

}
object IsInvariant {
  def apply[F[_]](implicit F: IsInvariant[F]): IsInvariant[F] = F

  def witness[F[_]](proof: F[Void] >~< F[Any]): IsInvariant[F] = new IsInvariant[F] {
    override def apply[A, B](implicit ev: A =!= B): F[A] >~< F[B] =
      Parametric[F].liftInv(StrictAs.bottomTop, proof, ev)
  }

  implicit def proposition[F[_]]: Proposition[IsInvariant[F]] =
    (A: ¬¬[IsInvariant[F]]) => new IsInvariant[F] {
      override def apply[A, B](implicit ev: A =!= B): F[A] >~< F[B] = A.map(_[A, B]).proved
    }
}