package io.cosmo.exo

import io.cosmo.exo.inhabitance.*
import io.cosmo.exo.evidence.*

opaque type Void <: Nothing = Nothing
object Void:
  def absurd[A](v: Void): A = v
  given isNotAny: =!=[Void, Any] = WeakApart.witness(_.flip(()))
  given uninhabited: ¬[Void] = Uninhabited.witness(identity[Void])
extension(v: Void)
  def absurd[A]: A = v

type Trivial[A] = DummyImplicit
object Trivial:
  def apply[A]: Trivial[A] = DummyImplicit.dummyImplicit
def trivial[A]: Trivial[A] = Trivial[A]

type VoidK[x] = Void
type VoidK2[x, y] = Void
type VoidHK[f[_]] = Void
type UnitK[x] = Unit
type UnitK2[x, y] = Unit
type UnitHK[f[_]] = Unit
type AnyK[x] = Any
type AnyK2[x, y] = Any
type AnyHK[f[_]] = Any

type <=>[A, B] = Iso[Function, A, B]
object `<=>`:
  def apply[A]: A <=> A = Iso.refl[A]
  def apply[A, B](using h: HasIso[Function, A, B]): A <=> B = h
  def unsafe[A, B](f: A => B, g: B => A): A <=> B = Iso.unsafe(f, g)

opaque type ~>[F[_], G[_]] >: [A] => F[A] => G[A] = [A] => F[A] => G[A]
object `~>`:
  extension [F[_], G[_]](fg: F ~> G)
    def exec[A](fa: F[A]): G[A] = fg(fa)
    def forall: ∀[[a] =>> F[a] => G[a]] = ∀.of[[a] =>> F[a] => G[a]].from(exec)
    def $(f: ∀[F]): ∀[G] = ∀.of[G].from(exec(f.apply))
    def andThen[H[_]](gh: G ~> H): F ~> H = [A] => (fa: F[A]) => gh(fg(fa))
    def compose[E[_]](ef: E ~> F): E ~> G = [A] => (ea: E[A]) => fg(ef(ea))
type <~[F[_], G[_]] = ~>[G, F]
opaque type <~>[F[_], G[_]] >: [A] => () => F[A] <=> G[A] = [A] => () => F[A] <=> G[A]
object `<~>`:
  def unsafe[F[_], G[_]](f: [A] => F[A] => G[A], g: [A] => G[A] => F[A]): F <~> G = [A] => () => Iso.unsafe(f[A], g[A])
  extension [F[_], G[_]](iso: F <~> G)
    def to:   F ~> G = [A] => (fa: F[A]) => iso[A]().to(fa)
    def from: G ~> F = [A] => (ga: G[A]) => iso[A]().from(ga)
    def flip: G <~> F = [A] => () => iso[A]().flip
    def andThen[H[_]](gh: G <~> H): F <~> H = [A] => () => iso[A]().andThen(gh[A]())

opaque type ~~>[F[_,_], G[_,_]] >: [A, B] => F[A, B] => G[A, B] = [A, B] => F[A, B] => G[A, B]
object `~~>`:
  def from[F[_,_], G[_,_]](fg: [A, B] => F[A, B] => G[A, B]): F ~~> G = fg
  extension[F[_,_], G[_,_] ](fg: F ~~> G)
    def exec[A, B](fab: F[A, B]): G[A, B] = fg(fab)
    def andThen[H[_,_]](gh: G ~~> H): F ~~> H = [A, B] => (fab: F[A, B]) => gh(fg(fab))
    def compose[E[_,_]](ef: E ~~> F): E ~~> G = [A, B] => (eab: E[A, B]) => fg(ef(eab))
type <~~[F[_,_], G[_,_]] = [A, B] => G[A, B] => F[A, B]
opaque type <~~>[F[_,_], G[_,_]] >: [A, B] => () => F[A, B] <=> G[A, B] = [A, B] => () => F[A, B] <=> G[A, B]
object `<~~>`:
  def unsafe[F[_,_], G[_,_]](fg: F ~~> G, gf: G ~~> F): F <~~> G =
    [A, B] => () => Iso.unsafe(fg[A, B], gf[A, B])
  extension[F[_,_], G[_,_]](iso: F <~~> G)
    def to:   F ~~> G = [A, B] => (fab: F[A, B]) => iso[A, B]().to(fab)
    def from: G ~~> F = [A, B] => (gab: G[A, B]) => iso[A, B]().from(gab)
    def flip: G <~~> F = [A, B] => () => iso[A, B]().flip

opaque type ≈>[A[_[_]], B[_[_]]] >: [F[_]] => A[F] => B[F] = [F[_]] => A[F] => B[F]
type <≈[A[_[_]], B[_[_]]] = [F[_]] => B[F] => A[F]
opaque type <≈>[A[_[_]], B[_[_]]] >: [F[_]] => () => A[F] <=> B[F] = [F[_]] => () => A[F] <=> B[F]
object `<≈>`:
  def unsafe[A[_[_]], B[_[_]]](ab: [F[_]] => A[F] => B[F], ba: [F[_]] => B[F] => A[F]): A <≈> B =
    [F[_]] => () => Iso.unsafe(ab[F], ba[F])
  extension[A[_[_]], B[_[_]]](iso: A <≈> B)
    def to:   A ≈> B = [F[_]] => (af: A[F]) => iso[F]().to(af)
    def from: B ≈> A = [F[_]] => (bf: B[F]) => iso[F]().from(bf)
    def flip: B <≈> A = [F[_]] => () => iso[F]().flip

opaque type ≈≈>[A[_[_],_[_]], B[_[_],_[_]]] >: [F[_], G[_]] => A[F, G] => B[F, G] = [F[_], G[_]] => A[F, G] => B[F, G]
type <≈≈[A[_[_],_[_]], B[_[_],_[_]]] = [F[_], G[_]] => B[F, G] => A[F, G]
opaque type <≈≈>[A[_[_],_[_]], B[_[_],_[_]]] >: [F[_], G[_]] => () => A[F, G] <=> B[F, G] = [F[_], G[_]] => () => A[F, G] <=> B[F, G]
object `<≈≈>`:
  def unsafe[A[_[_],_[_]], B[_[_],_[_]]](ab: [F[_], G[_]] => A[F, G] => B[F, G], ba: [F[_], G[_]] => B[F, G] => A[F, G]): A <≈≈> B =
    [F[_], G[_]] => () => Iso.unsafe(ab[F, G], ba[F, G])
  extension[A[_[_],_[_]], B[_[_],_[_]]](iso: A <≈≈> B)
    def to:   A ≈≈> B = [F[_], G[_]] => (af: A[F, G]) => iso[F, G]().to(af)
    def from: B ≈≈> A = [F[_], G[_]] => (bf: B[F, G]) => iso[F, G]().from(bf)
    def flip: B <≈≈> A = [F[_], G[_]] => () => iso[F, G]().flip
