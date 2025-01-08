package io.cosmo.exo.functors

import io.cosmo.exo.categories.*
import io.cosmo.exo.*

type Exo[==>[_,_], -->[_,_], F[_]] = Exofunctor[==>, -->, F]
val Exo = Exofunctor
type ExoK[==>[_,_], -->[_,_], A[_[_]]] = ExofunctorK[==>, -->, A]
val ExoK = ExofunctorK
type ExoK2[==>[_,_], -->[_,_], A[_[_,_]]] = ExofunctorK2[==>, -->, A]
val ExoK2 = ExofunctorK2
type ExoH[==>[_,_], -->[_,_], A[_[_[_]]]] = ExofunctorH[==>, -->, A]
val ExoH = ExofunctorH

type Exocon[==>[_,_], -->[_,_], F[_]] = Exofunctor[Dual[==>,*,*], -->, F]
object Exocon:
  def apply[==>[_,_], -->[_,_], F[_]](using E: Exocon[==>, -->, F]): Exocon[==>, -->, F] = E
  def unsafe[==>[_,_], -->[_,_], F[_]](fn: [a, b] => (a ==> b) => (F[b] --> F[a])): Exocon[==>, -->, F] =
    Exofunctor.unsafe([a,b] => (f: Dual[==>, a, b]) => fn(f.toFn))
type ExoconK[==>[_,_], -->[_,_], A[_[_]]] = ExofunctorK[Dual[==>,*,*], -->, A]
object ExoconK:
  def apply[==>[_,_], -->[_,_], A[_[_]]](using E: ExoconK[==>, -->, A]): ExoconK[==>, -->, A] = E
  def unsafe[==>[_,_], -->[_,_], A[_[_]]](fn: [F[_], G[_]] => ∀[[a] =>> F[a] ==> G[a]] => (A[G] --> A[F])): ExoconK[==>, -->, A] =
    ExofunctorK.unsafe([F[_], G[_]] => (f: ∀[[a] =>> Dual[==>, F[a], G[a]]]) => fn(f.toFnK))
type ExoconK2[==>[_,_], -->[_,_], A[_[_,_]]] = ExofunctorK2[Dual[==>,*,*], -->, A]
object ExoconK2:
  def apply[==>[_,_], -->[_,_], A[_[_,_]]](using E: ExoconK2[==>, -->, A]): ExoconK2[==>, -->, A] = E
  def unsafe[==>[_,_], -->[_,_], A[_[_,_]]](fn: [F[_,_], G[_,_]] => ∀∀[[a, b] =>> F[a, b] ==> G[a, b]] => (A[G] --> A[F])): ExoconK2[==>, -->, A] =
    ExofunctorK2.unsafe([F[_,_], G[_,_]] => (f: ∀∀[[a, b] =>> Dual[==>, F[a, b], G[a, b]]]) => fn(f.toFnK2))
type ExoconH[==>[_,_], -->[_,_], A[_[_[_]]]] = ExofunctorH[Dual[==>,*,*], -->, A]
object ExoconH:
  def apply[==>[_,_], -->[_,_], A[_[_[_]]]](using E: ExoconH[==>, -->, A]): ExoconH[==>, -->, A] = E
  def unsafe[==>[_,_], -->[_,_], A[_[_[_]]]](fn: [F[_[_]], G[_[_]]] => ∀~[[a[_]] =>> F[a] ==> G[a]] => (A[G] --> A[F])): ExoconH[==>, -->, A] =
    ExofunctorH.unsafe([F[_[_]], G[_[_]]] => (f: ∀~[[a[_]] =>> Dual[==>, F[a], G[a]]]) => fn(f.toFnH))

type FunctorK[A[_[_]]] = ExofunctorK[* => *, * => *, A]
object FunctorK:
  def apply[A[_[_]]](using E: FunctorK[A]): FunctorK[A] = E
type FunctorK2[A[_[_,_]]] = ExofunctorK2[* => *, * => *, A]
object FunctorK2:
  def apply[A[_[_,_]]](using E: FunctorK2[A]): FunctorK2[A] = E
type FunctorH[A[_[_[_]]]] = ExofunctorH[* => *, * => *, A]
object FunctorH:
  def apply[A[_[_[_]]]](using E: FunctorH[A]): FunctorH[A] = E

type ContravariantK[A[_[_]]] = ExofunctorK[Dual[* => *,*,*], * => *, A]
object ContravariantK:
  def apply[A[_[_]]](using E: ContravariantK[A]): ContravariantK[A] = E
type ContravariantK2[A[_[_,_]]] = ExofunctorK2[Dual[* => *,*,*], * => *, A]
object ContravariantK2:
  def apply[A[_[_,_]]](using E: ContravariantK2[A]): ContravariantK2[A] = E
type ContravariantH[A[_[_[_]]]] = ExofunctorH[Dual[* => *,*,*], * => *, A]
object ContravariantH:
  def apply[A[_[_[_]]]](using E: ContravariantH[A]): ContravariantH[A] = E

type Isofunctor[F[_]] = Exofunctor[<=>, <=>, F]
object Isofunctor:
  def apply[F[_]](using E: Isofunctor[F]): Isofunctor[F] = E
  trait Proto[F[_]] extends Exofunctor[<=>, <=>, F]:
    def map1[A, B](f: A <=> B): F[A] => F[B]
    def map[A, B](f: A <=> B): F[A] <=> F[B] = <=>.unsafe(map1(f), map1(f.flip))
type IsofunctorK[A[_[_]]] = ExofunctorK[<=>, <=>, A]
object IsofunctorK:
  def apply[A[_[_]]](using E: IsofunctorK[A]): IsofunctorK[A] = E
  trait Proto[A[_[_]]] extends ExofunctorK[<=>, <=>, A]:
    def map1[F[_], G[_]](i: ∀[[a] =>> F[a] <=> G[a]]): A[F] => A[G]
    def map[F[_], G[_]](i: ∀[[a] =>> F[a] <=> G[a]]): A[F] <=> A[G] = <=>.unsafe(map1(i), map1(i.flipK))
type IsofunctorK2[A[_[_,_]]] = ExofunctorK2[<=>, <=>, A]
object IsofunctorK2:
  def apply[A[_[_,_]]](using E: IsofunctorK2[A]): IsofunctorK2[A] = E
  trait Proto[A[_[_,_]]] extends ExofunctorK2[<=>, <=>, A]:
    def map1[F[_,_], G[_,_]](i: ∀∀[[a, b] =>> F[a, b] <=> G[a, b]]): A[F] => A[G]
    def map[F[_,_], G[_,_]](i: ∀∀[[a, b] =>> F[a, b] <=> G[a, b]]): A[F] <=> A[G] = <=>.unsafe(map1(i), map1(i.flipK2))
type IsofunctorH[A[_[_[_]]]] = ExofunctorH[<=>, <=>, A]
object IsofunctorH:
  def apply[A[_[_[_]]]](using E: IsofunctorH[A]): IsofunctorH[A] = E
  trait Proto[A[_[_[_]]]] extends ExofunctorH[<=>, <=>, A]:
    def map1[F[_[_]], G[_[_]]](i: ∀~[[a[_]] =>> F[a] <=> G[a]]): A[F] => A[G]
    def map[F[_[_]], G[_[_]]](i: ∀~[[a[_]] =>> F[a] <=> G[a]]): A[F] <=> A[G] = <=>.unsafe(map1(i), map1(i.flipH))

type Endofunctor[->[_,_], F[_]] = Exofunctor[->, ->, F]
object Endofunctor:
  /** This is isomorphic to cats.Functor[F] */
  type CovF[F[_]] = Endofunctor[* => *, F]
  def apply[->[_,_], F[_]](using E: Endofunctor[->, F]): Endofunctor[->, F] = E
  def unsafe[->[_,_], F[_]](fn: [a, b] => (a -> b) => (F[a] -> F[b])): Endofunctor[->, F] = Exofunctor.unsafe(fn)

type EndofunctorK[->[_,_], A[_[_]]] = ExofunctorK[->, ->, A]
object EndofunctorK:
  def apply[->[_,_], A[_[_]]](using E: EndofunctorK[->, A]): EndofunctorK[->, A] = E

type EndofunctorK2[->[_,_], A[_[_,_]]] = ExofunctorK2[->, ->, A]
object EndofunctorK2:
  def apply[->[_,_], A[_[_,_]]](using E: EndofunctorK2[->, A]): EndofunctorK2[->, A] = E

type EndofunctorH[->[_,_], A[_[_[_]]]] = ExofunctorH[->, ->, A]
object EndofunctorH:
  def apply[->[_,_], A[_[_[_]]]](using E: EndofunctorH[->, A]): EndofunctorH[->, A] = E

type Endobifunctor[->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]
object Endobifunctor:
  def apply[->[_,_], Bi[_,_]](using e: Endobifunctor[->, Bi]): Endobifunctor[->, Bi] = e
/** Endo bifunctor on scala function */
type EndobifunctorF[⊙[_,_]] = Endobifunctor[* => *, ⊙]
type Exoprofunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]] = Exobifunctor[Dual[==>,*,*], -->, >->, ⊙]
type Endoprofunctor[->[_,_], ⊙[_,_]] = Exobifunctor[Dual[->,*,*], ->, ->, ⊙]

type EndobifunctorK[->[_,_], ⊙[_[_],_[_]]] = ExobifunctorK[->, ->, ->, ⊙]
object EndobifunctorK:
  def apply[->[_,_], ⊙[_[_],_[_]]](using e: EndobifunctorK[->, ⊙]): EndobifunctorK[->, ⊙] = e
type EndobifunctorK2[->[_,_], ⊙[_[_,_],_[_,_]]] = ExobifunctorK2[->, ->, ->, ⊙]
object EndobifunctorK2:
  def apply[->[_,_], ⊙[_[_,_],_[_,_]]](using e: EndobifunctorK2[->, ⊙]): EndobifunctorK2[->, ⊙] = e
type EndobifunctorH[->[_,_], ⊙[_[_[_]],_[_[_]]]] = ExobifunctorH[->, ->, ->, ⊙]
object EndobifunctorH:
  def apply[->[_,_], ⊙[_[_[_]],_[_[_]]]](using e: EndobifunctorH[->, ⊙]): EndobifunctorH[->, ⊙] = e

type OplaxSemigroupal[=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxSemigroupal[=⊙, Dual[-->,*,*], -⊙, F]
type OplaxMonoidal   [=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxMonoidal   [=⊙, Dual[-->,*,*], -⊙, F]

type OplaxSemigroupalK[=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_]]] = LaxSemigroupalK[=⊙, Dual[-->,*,*], -⊙, A]
type OplaxMonoidalK   [=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_]]] = LaxMonoidalK   [=⊙, Dual[-->,*,*], -⊙, A]

type OplaxSemigroupalK2[=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_,_]]] = LaxSemigroupalK2[=⊙, Dual[-->,*,*], -⊙, A]
type OplaxMonoidalK2   [=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_,_]]] = LaxMonoidalK2   [=⊙, Dual[-->,*,*], -⊙, A]

type OplaxSemigroupalH[=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_[_]]]] = LaxSemigroupalH[=⊙, Dual[-->,*,*], -⊙, A]
type OplaxMonoidalH   [=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_[_]]]] = LaxMonoidalH   [=⊙, Dual[-->,*,*], -⊙, A]

type StrongSemigroupal[=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxSemigroupal[=⊙, Iso[-->,*,*], -⊙, F]
type StrongMonoidal   [=⊙[_,_], -->[_,_], -⊙[_,_], F[_]] = LaxMonoidal   [=⊙, Iso[-->,*,*], -⊙, F]

type StrongSemigroupalK[=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_]]] = LaxSemigroupalK[=⊙, Iso[-->,*,*], -⊙, A]
type StrongMonoidalK   [=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_]]] = LaxMonoidalK   [=⊙, Iso[-->,*,*], -⊙, A]

type StrongSemigroupalK2[=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_,_]]] = LaxSemigroupalK2[=⊙, Iso[-->,*,*], -⊙, A]
type StrongMonoidalK2   [=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_,_]]] = LaxMonoidalK2   [=⊙, Iso[-->,*,*], -⊙, A]

type StrongSemigroupalH[=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_[_]]]] = LaxSemigroupalH[=⊙, Iso[-->,*,*], -⊙, A]
type StrongMonoidalH   [=⊙[_,_], -->[_,_], -⊙[_,_], A[_[_[_]]]] = LaxMonoidalH   [=⊙, Iso[-->,*,*], -⊙, A]
