package io.cosmo.exo.internal

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.functors._
import io.cosmo.exo.syntax._
import io.cosmo.exo.internal.any._

trait FunctionKFunctions {
  private[this] type Id[A] = A

  def id[F[_]]: F ~> F = ∀.mk[F ~> F].from(identity)
  def andThen[F[_], G[_], H[_]](fg: F ~> G, gh: G ~> H): F ~> H = ∀.mk[F ~> H].fromH([T] => () => fg[T].andThen(gh[T]))
  def initiate [F[_]]: VoidK ~> F = ∀.mk[VoidK ~> F].from(identity)
  def terminate[F[_]]: F ~> UnitK = ∀.mk[F ~> UnitK].from(_ => ())
  def distribute[F[_], G[_], H[_]]: ([a] =>> (F[a], Either[G[a], H[a]])) ~> ([a] =>> Either[(F[a], G[a]), (F[a], H[a])]) =
    ∀.mk[([a] =>> (F[a], Either[G[a], H[a]])) ~> ([a] =>> Either[(F[a], G[a]), (F[a], H[a])])].from(Distributive[* => *, Tuple2, Either].distribute)
  object product {
    def associate  [F[_], G[_], H[_]]: ([a] =>> ((F[a], G[a]), H[a])) ~> ([a] =>> (F[a], (G[a], H[a]))) =
      ∀.mk[([a] =>> ((F[a], G[a]), H[a])) ~> ([a] =>> (F[a], (G[a], H[a])))].from(Associative[* => *, (*, *)].associate)
    def diassociate[F[_], G[_], H[_]]: ([a] =>> (F[a], (G[a], H[a]))) ~> ([a] =>> ((F[a], G[a]), H[a])) =
      ∀.mk[([a] =>> (F[a], (G[a], H[a]))) ~> ([a] =>> ((F[a], G[a]), H[a]))].from(Associative[* => *, (*, *)].diassociate)
    def bimap[F[_], G[_], X[_], Y[_]](fg: F ~> G, xy: X ~> Y): ([a] =>> (F[a], X[a])) ~> ([a] =>> (G[a], Y[a])) =
      ∀.mk[([a] =>> (F[a], X[a])) ~> ([a] =>> (G[a], Y[a]))].fromH([T] => () => Associative[* => *, (*, *)].grouped(fg[T], xy[T]))
    def fst[F[_], G[_]]: ([a] =>> (F[a], G[a])) ~> F = ∀.mk[([a] =>> (F[a], G[a])) ~> F].from(fg => fg._1)
    def snd[F[_], G[_]]: ([a] =>> (F[a], G[a])) ~> G = ∀.mk[([a] =>> (F[a], G[a])) ~> G].from(fg => fg._2)
    def diag[F[_]]: F ~> ([a] =>> (F[a], F[a])) = ∀.mk[F ~> ([a] =>> (F[a], F[a]))].from(f => (f, f))
    def merge[F[_], G[_], H[_]](f: F ~> G, g: F ~> H): F ~> ([a] =>> (G[a], H[a])) =
      ∀.mk[F ~> ([a] =>> (G[a], H[a]))].from(ft => (f.apply(ft), g.apply(ft)))
    def idl  [F[_]]: ([a] =>> (UnitK[a], F[a])) ~> F = ∀.mk[([a] =>> (UnitK[a], F[a])) ~> F].from(_._2)
    def idr  [F[_]]: ([a] =>> (F[a], UnitK[a])) ~> F = ∀.mk[([a] =>> (F[a], UnitK[a])) ~> F].from(_._1)
    def coidl[F[_]]: F ~> ([a] =>> (UnitK[a], F[a])) = ∀.mk[F ~> ([a] =>> (UnitK[a], F[a]))].from(((), _))
    def coidr[F[_]]: F ~> ([a] =>> (F[a], UnitK[a])) = ∀.mk[F ~> ([a] =>> (F[a], UnitK[a]))].from((_, ()))
    def braid[F[_], G[_]]: ([a] =>> (F[a], G[a])) ~> ([a] =>> (G[a], F[a])) =
      ∀.mk[([a] =>> (F[a], G[a])) ~> ([a] =>> (G[a], F[a]))].from(_.swap)
    def curry[F[_], G[_], H[_]](f: ∀[[a] =>> ((F[a], G[a])) => H[a]]): ∀[[a] =>> F[a] => G[a] => H[a]] =
      ∀.of[[a] =>> F[a] => G[a] => H[a]].from(fa => ga => f.apply(fa, ga))
    def uncurry[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] => G[a] => H[a]]): ∀[[a] =>> ((F[a], G[a])) => H[a]] =
      ∀.of[[a] =>> ((F[a], G[a])) => H[a]].from(fg => f.apply(fg._1).apply(fg._2))
  }
  object coproduct {
    def diassociate[F[_], G[_], H[_]]: ([a] =>> Either[Either[F[a], G[a]], H[a]]) ~> ([a] =>> Either[F[a], Either[G[a], H[a]]]) =
      ∀.mk[([a] =>> Either[Either[F[a], G[a]], H[a]]) ~> ([a] =>> Either[F[a], Either[G[a], H[a]]])].from(Associative[* => *, Either].associate)
    def associate[F[_], G[_], H[_]]: ([a] =>> Either[F[a], Either[G[a], H[a]]]) ~> ([a] =>> Either[Either[F[a], G[a]], H[a]]) =
      ∀.mk[([a] =>> Either[F[a], Either[G[a], H[a]]]) ~> ([a] =>> Either[Either[F[a], G[a]], H[a]])].from(Associative[* => *, Either].diassociate)
    def bimap[F[_], G[_], X[_], Y[_]](fg: F ~> G, xy: X ~> Y): ([a] =>> Either[F[a], X[a]]) ~> ([a] =>> Either[G[a], Y[a]]) =
      ∀.mk[([a] =>> Either[F[a], X[a]]) ~> ([a] =>> Either[G[a], Y[a]])].fromH([T] => () => Associative[* => *, Either].grouped(fg[T], xy[T]))
    def inl[F[_], G[_]]: F ~> ([a] =>> Either[F[a], G[a]]) = ∀.mk[F ~> ([a] =>> Either[F[a], G[a]])].from(_.asLeft)
    def inr[F[_], G[_]]: G ~> ([a] =>> Either[F[a], G[a]]) = ∀.mk[G ~> ([a] =>> Either[F[a], G[a]])].from(_.asRight)
    def codiag[F[_]]: ([a] =>> Either[F[a], F[a]]) ~> F = ∀.mk[([a] =>> Either[F[a], F[a]]) ~> F].from(_.fold(identity, identity))
    def split[F[_], G[_], H[_]](f: F ~> H, g: G ~> H): ([a] =>> Either[F[a], G[a]]) ~> H =
      ∀.mk[([a] =>> Either[F[a], G[a]]) ~> H].from(_.fold(f.apply, g.apply))
    def coidl[F[_]]: ([a] =>> Either[VoidK[a], F[a]]) ~> F = ∀.mk[([a] =>> Either[VoidK[a], F[a]]) ~> F].from(_.fold(identity, identity))
    def coidr[F[_]]: ([a] =>> Either[F[a], VoidK[a]]) ~> F = ∀.mk[([a] =>> Either[F[a], VoidK[a]]) ~> F].from(_.fold(identity, identity))
    def idl  [F[_]]: F ~> ([a] =>> Either[VoidK[a], F[a]]) = ∀.mk[F ~> ([a] =>> Either[VoidK[a], F[a]])].from(_.asRight)
    def idr  [F[_]]: F ~> ([a] =>> Either[F[a], VoidK[a]]) = ∀.mk[F ~> ([a] =>> Either[F[a], VoidK[a]])].from(_.asLeft)
    def braid[F[_], G[_]]: ([a] =>> Either[F[a], G[a]]) ~> ([a] =>> Either[G[a], F[a]]) =
      ∀.mk[([a] =>> Either[F[a], G[a]]) ~> ([a] =>> Either[G[a], F[a]])].from(_.swap)
  }
  object composition {
    def bimap[F[_], G[_], X[_], Y[_]](fg: F ~> G, xy: X ~> Y)(using
      E: Exo.Cov[* => *, F]
    ): ([a] =>> F[X[a]]) ~> ([a] =>> G[Y[a]]) =
      ∀.mk[([a] =>> F[X[a]]) ~> ([a] =>> G[Y[a]])].fromH([T] => () => fxa => fg.apply(E.map(xy.apply[T])(fxa)))
    def associate  [F[_], G[_], H[_]]: ([a] =>> F[G[H[a]]]) ~> ([a] =>> F[G[H[a]]]) =
      ∀.mk[([a] =>> F[G[H[a]]]) ~> ([a] =>> F[G[H[a]]])].from(identity)
    def diassociate[F[_], G[_], H[_]]: ([a] =>> F[G[H[a]]]) ~> ([a] =>> F[G[H[a]]]) =
      ∀.mk[([a] =>> F[G[H[a]]]) ~> ([a] =>> F[G[H[a]]])].from(identity)
    def idl  [F[_]]: ([a] =>> Id[F[a]]) ~> F = id[F]
    def idr  [F[_]]: ([a] =>> F[Id[a]]) ~> F = id[F]
    def coidl[F[_]]: F ~> ([a] =>> Id[F[a]]) = id[F]
    def coidr[F[_]]: F ~> ([a] =>> F[Id[a]]) = id[F]
  }
}
