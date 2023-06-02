package io.cosmo.exo.evidence

import io.cosmo.exo.*
import io.cosmo.exo.variance.*
import io.cosmo.exo.inhabitance.*

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
    Axioms.parametricity1[F, A, B, A, B](ev, contrapositive(ev.notEqual), ev.notEqual)


  /**
   * F is injective if and only if, given any G, H whenever F ∘ G = F ∘ H, then G = H.
   * In other words, injective type constructors are precisely the monomorphisms in the category
   * of types and type constructors.
   */
  def monomorphism[G[_], H[_]](p: ([x] =>> F[G[x]]) =~= ([x] =>> F[H[x]])): G =~= H =
    Axioms.tcExtensionality[G, H].applyT([T] => () => F[G[T], H[T]](p.lower[[x[_]] =>> x[T]]))

  /**
   * If A ≠ B, then F[A] ≠ F[B].
   */
  def contrapositive[A, B](ev: A =!= B): F[A] =!= F[B] =
    WeakApart.witness[F[A], F[B]] { fab => ev.run(F(fab)) }

  /**
   * If G ∘ F is injective, then F is injective (but G need not be).
   */
  def decompose[G[_], H[_]](using p: F =~= ([x] =>> G[H[x]])): IsInjective[H] = {
    val GH: IsInjective[[x] =>> G[H[x]]] = p.subst[IsInjective](F)

    new IsInjective[H] {
      override def apply[A, B](implicit ev: H[A] === H[B]): A === B =
        GH(ev.lift[G])

      override def monomorphism[I[_], J[_]](p: ([x] =>> H[I[x]]) =~= ([x] =>> H[J[x]])): I =~= J = {
        type f[x[_], a] = G[x[a]]
        val q : ([x] =>> G[H[I[x]]]) =~= ([x] =>> G[H[J[x]]]) = p.lift[f]
        GH.monomorphism[I, J](q)
      }
    }
  }


  /**
   * If F and G are both injective, then F ∘ G is injective.
   */
  def compose[G[_]](implicit G: IsInjective[G]): IsInjective[[x] =>> F[G[x]]] =
    new IsInjective.Compose[F, G](F, G)

  /**
   * If F and G are both injective, then G ∘ F is injective.
   */
  def andThen[G[_]](implicit G: IsInjective[G]): IsInjective[[x] =>> G[F[x]]] =
    new IsInjective.Compose[G, F](G, F)

}

object IsInjective {
  def apply[F[_]](implicit F: IsInjective[F]): IsInjective[F] = F

  type Canonic[F[_]] = [a,b] => (F[a] === F[b]) => (a === b)

  implicit def isoCanonic[F[_]]: Canonic[F] <=> IsInjective[F] =
    <=>.unsafe[Canonic[F], IsInjective[F]](
      can => new IsInjective[F] { def apply[A, B](implicit ev: F[A] === F[B]): A === B = can[A, B](ev) },
      isi => [a, b] => (ev: F[a] === F[b]) => isi.apply(ev)
    )

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

  final case class Compose[F[_], G[_]](F: IsInjective[F], G: IsInjective[G]) extends IsInjective[[x] =>> F[G[x]]] {
    override def apply[A, B](implicit ev: F[G[A]] === F[G[B]]): A === B =
      G[A, B](F[G[A], G[B]](ev))
  }

  implicit def proposition[F[_]]: Proposition[IsInjective[F]] =
    Proposition.witness {
      (A: ¬¬[IsInjective[F]]) => new IsInjective[F] {
        override def apply[A, B](using ev: F[A] === F[B]): A === B =
          Proposition[A === B].proved(using A.map(inj => inj.apply[A, B]))
      }
    }

}
