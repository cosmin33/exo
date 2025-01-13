package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.inhabitance.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

type Void <: Nothing with Void.Tag
object Void:
  private[exo] trait Tag extends Any
  given isNotAny: (Void =!= Any) = WeakApart.witness(_.flip(()))
  given uninhabited: ¬[Void] = Uninhabited.witness(identity[Void])
  extension(v: Void)
    def absurd[A]: A = v

opaque type Trivial[A] = Unit
object Trivial:
  def apply[A]: Trivial[A] = ()
  given [A]: Trivial[A] = ()
  given [F[_]]    : TrivialK[F]  = TrivialK[F]
  given [F[_,_]]  : TrivialK2[F] = TrivialK2[F]
  given [F[_,_,_]]: TrivialK3[F] = TrivialK3[F]
  given [A[_[_]]] : TrivialH[A]  = TrivialH[A]
type TrivialK[F[_]] = ∀[[a] =>> Trivial[F[a]]]
object TrivialK:
  def apply[F[_]]: TrivialK[F] = ∀.of[[a] =>> Trivial[F[a]]].from(())
type TrivialK2[F[_,_]] = ∀∀[[a, b] =>> Trivial[F[a, b]]]
object TrivialK2:
  def apply[F[_,_]]: TrivialK2[F] = ∀∀.of[[a, b] =>> Trivial[F[a, b]]].from(())
type TrivialK3[F[_,_,_]] = ∀∀∀[[a, b, c] =>> Trivial[F[a, b, c]]]
object TrivialK3:
  def apply[F[_,_,_]]: TrivialK3[F] = ∀∀∀.of[[a, b, c] =>> Trivial[F[a, b, c]]].from(())
type TrivialH[A[_[_]]] = ∀~[[f[_]] =>> Trivial[A[f]]]
object TrivialH:
  def apply[A[_[_]]]: TrivialH[A] = ∀~.of[[f[_]] =>> Trivial[A[f]]].from(())

type VoidK[x] = Void
type VoidK2[x, y] = Void
type VoidH[f[_]] = Void
type UnitK[x] = Unit
type UnitK2[x, y] = Unit
type UnitH[f[_]] = Unit
type AnyK[x] = Any
type AnyK2[x, y] = Any
type AnyH[f[_]] = Any

type IsoK[->[_,_], F[_], G[_]] = ∀[[a] =>> Iso[->, F[a], G[a]]]
type IsoK2[->[_,_], F[_,_], G[_,_]] = ∀∀[[a, b] =>> Iso[->, F[a, b], G[a, b]]]
type IsoH[->[_,_], A[_[_]], B[_[_]]] = ∀~[[f[_]] =>> Iso[->, A[f], B[f]]]

object IsoK:
  def unsafe[->[_,_], F[_], G[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> G[a] -> F[a]])(using s: Semicategory[->]): IsoK[->, F, G] =
    ∀.mk[IsoK[->, F, G]].fromH([a] => () => Iso.unsafe(f[a], g[a]))
  def refl[->[_,_], F[_]](using s: SubcatKHasId[->, F]): IsoK[->, F, F] = ??? //∀.mk[IsoK[->, F, F]].from(Iso.refl)

object IsoK2:
  def unsafe[->[_,_], F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> G[a, b] -> F[a, b]])(using s: Semicategory[->]): IsoK2[->, F, G] =
    ∀∀.mk[IsoK2[->, F, G]].fromH([a, b] => () => Iso.unsafe(f[a, b], g[a, b]))
  def refl[->[_,_], F[_,_]](using s: SubcatK2HasId[->, F]): IsoK2[->, F, F] = ??? //∀∀.mk[IsoK2[->, F]].from(Iso.refl)

object IsoH:
  def unsafe[->[_,_], A[_[_]], B[_[_]]](f: ∀~[[F[_]] =>> A[F] -> B[F]], g: ∀~[[F[_]] =>> B[F] -> A[F]])(using s: Semicategory[->]): IsoH[->, A, B] =
    ∀~.mk[IsoH[->, A, B]].fromH([F[_]] => () => Iso.unsafe(f[F], g[F]))
  def refl[->[_,_], A[_[_]]](using s: SubcatHHasId[->, A]): IsoH[->, A, A] = ??? //∀~.mk[IsoH[->, A]].from(Iso.refl)

type <=>[A, B] = Iso[Function, A, B]

type ~> [F[_], G[_]] = ∀[[a] =>> F[a] => G[a]]
type <~ [F[_], G[_]] = G ~> F
type <~>[F[_], G[_]] = IsoK[* => *, F, G]

type ~~> [F[_,_], G[_,_]] = ∀∀[[a, b] =>> F[a, b] => G[a, b]]
type <~~ [F[_,_], G[_,_]] = G ~~> F
type <~~>[F[_,_], G[_,_]] = IsoK2[* => *, F, G]

type ≈> [A[_[_]], B[_[_]]] = ∀~[[f[_]] =>> A[f] => B[f]]
type <≈ [A[_[_]], B[_[_]]] = B ≈> A
type <≈>[A[_[_]], B[_[_]]] = IsoH[* => *, A, B]

object `<=>`:
  def apply[A]: A <=> A = Iso.refl[A]
  def apply[A, B](using h: HasIso[Function, A, B]): A <=> B = h
  def unsafe[A, B](f: A => B, g: B => A): A <=> B = Iso.unsafe(f, g)

object `~>` extends FunctionKFunctions:
  def apply[F[_], G[_]](fg: [A] => F[A] => G[A]): F ~> G = ∀.mk[F ~> G].fromH([A] => () => fg[A])
object `<~>`:
  def apply[F[_]]: F <~> F = apply[F, F]
  def apply[F[_], G[_]](using h: HasIsoK[* => *, F, G]): F <~> G = h
  def unsafe[F[_], G[_]](f: [A] => F[A] => G[A], g: [A] => G[A] => F[A]): F <~> G = IsoK.unsafe(~>(f), ~>(g))
  def unsafe[F[_], G[_]](f: F ~> G, g: G ~> F): F <~> G = IsoK.unsafe(f, g)

object `~~>` extends FunctionK2Functions:
  def apply[F[_,_], G[_,_]](fg: [A, B] => F[A, B] => G[A, B]): F ~~> G = ∀∀.mk[F ~~> G].fromH([A, B] => () => fg[A, B])
object `<~~>`:
  def apply[F[_,_]]: F <~~> F = apply[F, F]
  def apply[F[_,_], G[_,_]](using h: HasIsoK2[Function, F, G]): F <~~> G = h
  def unsafe[F[_,_], G[_,_]](f: [A, B] => F[A, B] => G[A, B], g: [A, B] => G[A, B] => F[A, B]): F <~~> G = IsoK2.unsafe(~~>(f), ~~>(g))
  def unsafe[F[_,_], G[_,_]](fg: F ~~> G, gf: G ~~> F): F <~~> G = IsoK2.unsafe(fg, gf)

object `≈>` extends FunctionHKFunctions:
  def apply[A[_[_]], B[_[_]]](ab: [F[_]] => A[F] => B[F]): A ≈> B = ∀~.mk[A ≈> B].fromH([F[_]] => () => ab[F])
object `<≈>`:
  def apply[A[_[_]]]: A <≈> A = apply[A, A]
  def apply[A[_[_]], B[_[_]]](using h: HasIsoH[* => *, A, B]): A <≈> B = h
  def unsafe[A[_[_]], B[_[_]]](f: [F[_]] => A[F] => B[F], g: [F[_]] => B[F] => A[F]): A <≈> B = IsoH.unsafe(≈>(f), ≈>(g))
  def unsafe[A[_[_]], B[_[_]]](f: A ≈> B, g: B ≈> A): A <≈> B = IsoH.unsafe(f, g)
