package io.cosmo.exo.evidence

import io.cosmo.exo.{<=>, Iso, Void, ∀∀}
import io.cosmo.exo.evidence.variance.IsConstant
import cats.implicits._

trait IsInjective[F[_]] { F =>

  /**
   * The function f is said to be injective provided that for all a and b in X,
   * whenever f(a) = f(b), then a = b.
   */
  def apply[A, B](implicit ev: F[A] === F[B]): A === B

  /**
   * Constant type constructors are not injective.
   */
  def notConstant(cF: IsConstant[F]): Void =
    F(cF[Unit, Void]).coerce(())

  def incomparable[A, B](ev: A >~< B): F[A] >~< F[B] =
    Parametric[F].liftInc[A, B, A, B](ev, contrapositive(ev.notEqual), ev.notEqual)


  /**
   * F is injective if and only if, given any G, H whenever F ∘ G = F ∘ H, then G = H.
   * In other words, injective type constructors are precisely the monomorphisms in the category
   * of types and type constructors.
   */
  def monomorphism[G[_], H[_]](p: λ[x => F[G[x]]] =~= λ[x => F[H[x]]]): G =~= H =
    Axioms.tcExtensionality[G, H].applyT { t => type T = t.Type
      F[G[T], H[T]](p.lower[λ[x[_] => x[T]]])
    }

  /**
   * If A ≠ B, then F[A] ≠ F[B].
   */
  def contrapositive[A, B](ev: A =!= B): F[A] =!= F[B] =
    WeakApart.witness[F[A], F[B]] { fab => ev(F(fab)) }

  /**
   * If G ∘ F is injective, then F is injective (but G need not be).
   */
  def decompose[G[_], H[_]](implicit p: F =~= λ[x => G[H[x]]]): IsInjective[H] = {
    val GH: IsInjective[λ[x => G[H[x]]]] = p.subst[IsInjective](F)

    new IsInjective[H] {
      override def apply[A, B](implicit ev: H[A] === H[B]): A === B =
        GH(ev.lift[G])

      override def monomorphism[I[_], J[_]](p: λ[x => H[I[x]]] =~= λ[x => H[J[x]]]): I =~= J = {
        type f[x[_], a] = G[x[a]]
        val q : λ[x => G[H[I[x]]]] =~= λ[x => G[H[J[x]]]] = p.lift[f]
        GH.monomorphism[I, J](q)
      }
    }
  }


  /**
   * If F and G are both injective, then F ∘ G is injective.
   */
  def compose[G[_]](implicit G: IsInjective[G]): IsInjective[λ[x => F[G[x]]]] =
    new IsInjective.Compose[F, G](F, G)

  /**
   * If F and G are both injective, then G ∘ F is injective.
   */
  def andThen[G[_]](implicit G: IsInjective[G]): IsInjective[λ[x => G[F[x]]]] =
    new IsInjective.Compose[G, F](G, F)

}

object IsInjective {
  type Canonic[F[_]] = ∀∀[λ[(a,b) => (F[a] === F[b]) => (a === b)]]

  def apply[F[_]](implicit F: IsInjective[F]): IsInjective[F] = F

  def isoCanonic[F[_]]: Canonic[F] <=> IsInjective[F] = ???

  implicit def witness[F[_]](implicit fnab: F[Void] =!= F[Any]): IsInjective[F] =
    witness1[F, Void, Any](fnab)

  def witness1[F[_], A, B](fnab: F[A] =!= F[B]): IsInjective[F] = new IsInjective[F] {
    override def apply[X, Y](implicit ev: F[X] === F[Y]): X === Y =
      Parametric[F].lowerInj[A, B, X, Y](fnab, ev)
  }

  def witness2[F[_], G[_], A, B](x: G[F[A]], y: G[F[B]] => Void): IsInjective[F] =
    witness1[F, A, B](WeakApart.witness( ab => {
      type f[x] = G[x]
      y(ab.subst[f](x))
    }))

  def witness3[F[_], G[_], A, B](x: Inhabited[G[F[A]]], y: Uninhabited[G[F[B]]]): IsInjective[F] =
    witness1[F, A, B](WeakApart.witness( ab => {
      type f[x] = Inhabited[G[x]]
      ab.subst[f](x).notUninhabited(y)
    }))

  def viaRetraction[F[_], R[_ <: F[_]]](retraction: λ[x => R[F[x]]] =~= λ[x => x]): IsInjective[F] =
    witness1[F, Void, Unit](WeakApart.witness(
      (ab: F[Void] === F[Unit]) => {
        val p = Leibniz.fromIs[Nothing, F[_], F[Void], F[Unit]](ab)
        val r: R[F[Unit]] === R[F[Void]] = p.lift[Nothing, Any, R].toIs.flip
        val q: R[F[Void]] === Void = retraction.lower[λ[x[_] => x[Void]]]
        val s: Unit === R[F[Unit]] = retraction.flip.lower[λ[x[_] => x[Unit]]]
        (s andThen r andThen q).coerce(())
      }
    ))

  final case class Compose[F[_], G[_]](F: IsInjective[F], G: IsInjective[G]) extends IsInjective[λ[x => F[G[x]]]] {
    override def apply[A, B](implicit ev: F[G[A]] === F[G[B]]): A === B =
      G[A, B](F[G[A], G[B]](ev))
  }

  implicit def proposition[F[_]]: Proposition[IsInjective[F]] =
    (A: ¬¬[IsInjective[F]]) => new IsInjective[F] {
      override def apply[A, B](implicit ev: F[A] === F[B]): A === B =
        Proposition[A === B].proved(A.map(inj => inj.apply[A, B]))
//        Proposition[A === B].proved(A.map(_[A, B]))
    }

}
