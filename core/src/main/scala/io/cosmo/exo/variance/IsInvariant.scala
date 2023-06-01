package io.cosmo.exo.variance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.inhabitance.*

trait IsInvariant[F[_]] { F =>
  def apply[A, B](using ev: A =!= B): F[A] >~< F[B]

  def injective: IsInjective[F] =
    IsInjective.witness[F](using F(using Void.isNotAny).notEqual)

  def composePh[G[_]](G: IsConstant[G]): IsConstant[[x] =>> F[G[x]]] =
    IsConstant.witness[[x] =>> F[G[x]]](using G[Void, Any].lift[F])

  def composeInj[G[_]](G: IsInjective[G]): IsInvariant[[x] =>> F[G[x]]] =
    IsInvariant.witness[[x] =>> F[G[x]]](using F(using G.contrapositive(Void.isNotAny)))

  def composeStCv[G[_]](G: StrictlyCovariant[G]): IsInvariant[[x] =>> F[G[x]]] =
    IsInvariant.witness[[x] =>> F[G[x]]](using F(using G.injective.contrapositive(Void.isNotAny)))

  def composeStCt[G[_]](G: StrictlyContravariant[G]): IsInvariant[[x] =>> F[G[x]]] =
    IsInvariant.witness[[x] =>> F[G[x]]](using F(using G.injective.contrapositive(Void.isNotAny)))

  def composeInv [G[_]](G: IsInvariant[G]): IsInvariant[[x] =>> F[G[x]]] =
    IsInvariant.witness[[x] =>> F[G[x]]](using F(using G(using Void.isNotAny).notEqual))

}
object IsInvariant {
  def apply[F[_]](using F: IsInvariant[F]): IsInvariant[F] = F

  def isoCanonic[F[_]]: Exo[=!=, >~<, F] <=> IsInvariant[F] =
    Iso.unsafe(
      exo => new IsInvariant[F] { def apply[A, B](using ev: A =!= B) = exo.map(ev) },
      isi => Exo.unsafe([A, B] => (neq: A =!= B) => isi(using neq))
    )

  def witness[F[_]](using proof: F[Void] >~< F[Any]): IsInvariant[F] =
    new IsInvariant[F]:
      def apply[A, B](using ev: A =!= B): F[A] >~< F[B] = Parametric[F].liftInv(StrictAs.bottomTop, proof, ev)

  given proposition[F[_]]: Proposition[IsInvariant[F]] =
    Proposition.witness((A: ¬¬[IsInvariant[F]]) => new IsInvariant[F] {
      def apply[A, B](using ev: A =!= B): F[A] >~< F[B] = A.map(_[A, B]).proved
    })
}