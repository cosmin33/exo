package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.inhabitance.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

type Void <: Nothing with Void.Tag
object Void:
  private[exo] trait Tag extends Any
  def absurd[A](v: Void): A = v
  given isNotAny: (Void =!= Any) = WeakApart.witness(_.flip(()))
  given uninhabited: ¬[Void] = Uninhabited.witness(identity[Void])
extension(v: Void)
  def absurd[A]: A = v

opaque type Trivial[A] = Unit
object Trivial:
  def apply[A]: Trivial[A] = ()
  given [A]: Trivial[A] = ()
  given [F[_]]:       ∀[[a]       =>> Trivial[F[a]]]       = ∀.of[[a] =>> Trivial[F[a]]].from(apply)
  given [F[_,_]]:    ∀∀[[a, b]    =>> Trivial[F[a, b]]]    = ∀∀.of[[a, b] =>> Trivial[F[a, b]]].from(apply)
  given [F[_,_,_]]: ∀∀∀[[a, b, c] =>> Trivial[F[a, b, c]]] = ∀∀∀.of[[a, b, c] =>> Trivial[F[a, b, c]]].from(apply)
  given [A[_[_]]]:   ∀~[[f[_]]    =>> Trivial[A[f]]]       = ∀~.of[[f[_]] =>> Trivial[A[f]]].from(apply)

type VoidK[x] = Void
type VoidK2[x, y] = Void
type VoidHK[f[_]] = Void
type UnitK[x] = Unit
type UnitK2[x, y] = Unit
type UnitHK[f[_]] = Unit
type AnyK[x] = Any
type AnyK2[x, y] = Any
type AnyHK[f[_]] = Any

type IsoFunK[A, B] = Iso[FunK, A, B]
object IsoFunK:
  def apply[F[_], G[_]](i: F <~> G): IsoFunK[TypeK[F], TypeK[G]] = Iso.unsafe[FunK, TypeK[F], TypeK[G]](FunK(i.to), FunK(i.from))
  
type IsoFunK2[A, B] = Iso[FunK2, A, B]
object IsoFunK2:
  def apply[F[_,_], G[_,_]](i: F <~~> G): IsoFunK2[TypeK2[F], TypeK2[G]] = Iso.unsafe[FunK2, TypeK2[F], TypeK2[G]](FunK2(i.to), FunK2(i.from))

type IsoFunH[A, B] = Iso[FunH, A, B]
object IsoFunH:
  def apply[A[_[_]], B[_[_]]](i: A <≈> B): IsoFunH[TypeHK[A], TypeHK[B]] = Iso.unsafe[FunH, TypeHK[A], TypeHK[B]](FunH(i.to), FunH(i.from))

type IsoK [->[_,_], F[_],    G[_]]    =  ∀[[a]    =>> Iso[->, F[a], G[a]]]
type IsoK2[->[_,_], F[_,_],  G[_,_]]  = ∀∀[[a, b] =>> Iso[->, F[a, b], G[a, b]]]
type IsoHK[->[_,_], A[_[_]], B[_[_]]] = ∀~[[f[_]] =>> Iso[->, A[f], B[f]]]

object IsoK:
  def unsafe[->[_,_], F[_], G[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> G[a] -> F[a]])(using s: Subcat[->]): IsoK[->, F, G] =
    ∀.mk[IsoK[->, F, G]].fromH([a] => () => Iso.unsafe(f[a], g[a]))

object IsoK2:
  def unsafe[->[_,_], F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> G[a, b] -> F[a, b]])(using s: Subcat[->]): IsoK2[->, F, G] =
    ∀∀.mk[IsoK2[->, F, G]].fromH([a, b] => () => Iso.unsafe(f[a, b], g[a, b]))

object IsoHK:
  def unsafe[->[_,_], A[_[_]], B[_[_]]](f: ∀~[[F[_]] =>> A[F] -> B[F]], g: ∀~[[F[_]] =>> B[F] -> A[F]])(using s: Subcat[->]): IsoHK[->, A, B] =
    ∀~.mk[IsoHK[->, A, B]].fromH([F[_]] => () => Iso.unsafe(f[F], g[F]))

infix type <=>[A, B] = Iso[Function, A, B]
object `<=>`:
  def apply[A]: A <=> A = Iso.refl[A]
  def apply[A, B](using h: HasIso[Function, A, B]): A <=> B = h
  def unsafe[A, B](f: A => B, g: B => A): A <=> B = Iso.unsafe(f, g)

infix type ~>[F[_], G[_]] = ∀[[a] =>> F[a] => G[a]]
object `~>` extends FunctionKFunctions:
  def apply[F[_], G[_]](fg: [A] => F[A] => G[A]): F ~> G = ∀.mk[F ~> G].fromH([A] => () => fg[A])
infix type <~[F[_], G[_]] = ~>[G, F]

infix type <~>[F[_], G[_]] = ∀[[α] =>> F[α] <=> G[α]]
object `<~>`:
  def apply[F[_]]: F <~> F = apply[F, F]
  def apply[F[_], G[_]](using h: HasIsoK[_ => _, F, G]): F <~> G = h
  def unsafe[F[_], G[_]](f: [A] => F[A] => G[A], g: [A] => G[A] => F[A]): F <~> G =
    ∀.mk[F <~> G].fromH([a] => () => Iso.unsafe(f[a], g[a]))
  def unsafe[F[_], G[_]](f: F ~> G, g: G ~> F): F <~> G = ∀.mk[F <~> G].from(Iso.unsafe(f.apply, g.apply))
  def unsafe[F[_], G[_]](i: [A] => () => F[A] <=> G[A]): F <~> G = ∀.mk[F <~> G].fromH(i)

infix type ~~>[F[_,_], G[_,_]] = ∀∀[[a, b] =>> F[a, b] => G[a, b]]
object `~~>` extends FunctionK2Functions:
  def apply[F[_,_], G[_,_]](fg: [A, B] => F[A, B] => G[A, B]): F ~~> G = ∀∀.mk[F ~~> G].fromH([A, B] => () => fg[A, B])
infix type <~~[F[_,_], G[_,_]] = ~~>[G, F]

infix type <~~>[F[_,_], G[_,_]] = ∀∀[[a, b] =>> F[a, b] <=> G[a, b]]
object `<~~>`:
  def apply[F[_,_]]: F <~~> F = apply[F, F]
  def apply[F[_,_], G[_,_]](using h: HasIsoK2[Function, F, G]): F <~~> G = h
  def unsafe[F[_,_], G[_,_]](f: [A, B] => F[A, B] => G[A, B], g: [A, B] => G[A, B] => F[A, B]): F <~~> G =
    ∀∀.mk[F <~~> G].fromH([a,b] => () => Iso.unsafe(f[a,b], g[a,b]))
  def unsafe[F[_,_], G[_,_]](fg: F ~~> G, gf: G ~~> F): F <~~> G = ∀∀.mk[F <~~> G].from(Iso.unsafe(fg.apply, gf.apply))
  def unsafe[F[_,_], G[_,_]](i: [A, B] => () => F[A, B] <=> G[A, B]): F <~~> G = ∀∀.mk[F <~~> G].fromH(i)

infix type ≈>[A[_[_]], B[_[_]]] = ∀~[[f[_]] =>> A[f] => B[f]]
object `≈>` extends FunctionHKFunctions:
  def apply[A[_[_]], B[_[_]]](ab: [F[_]] => A[F] => B[F]): A ≈> B = ∀~.mk[A ≈> B].fromH([F[_]] => () => ab[F])
infix type <≈[A[_[_]], B[_[_]]] = B ≈> A

infix type <≈>[A[_[_]], B[_[_]]] = ∀~[[f[_]] =>> A[f] <=> B[f]]
object `<≈>`:
  def unsafe[A[_[_]], B[_[_]]](ab: [F[_]] => A[F] => B[F], ba: [F[_]] => B[F] => A[F]): A <≈> B =
    ∀~.mk[A <≈> B].fromH([f[_]] => () => Iso.unsafe(ab[f], ba[f]))
  def unsafe[A[_[_]], B[_[_]]](f: A ≈> B, g: B ≈> A): A <≈> B = ∀~.mk[A <≈> B].from(Iso.unsafe(f.apply, g.apply))
  def unsafe[A[_[_]], B[_[_]]](i: [F[_]] => () => A[F] <=> B[F]): A <≈> B = ∀~.mk[A <≈> B].fromH(i)
