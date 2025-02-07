package io.cosmo.exo.categories

import io.cosmo.exo
import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

trait Cartesian[->[_,_], ⨂[_,_]] extends Monoidal[->, ⨂] with Symmetric[->, ⨂]:
  def fst[A: TC, B: TC]: ⨂[A, B] -> A
  def snd[A: TC, B: TC]: ⨂[A, B] -> B
  def diag[A: TC]: A -> ⨂[A, A]
  
  def &&&[A, B, C](f: A -> B, g: A -> C): A -> ⨂[B, C]
  // this is almost the same, just that it requires the typeclass defined for the first parameter
  private def &&&&[A: TC, B, C](f: A -> B, g: A -> C): A -> ⨂[B, C] = C.andThen(diag[A], bifunctor.bimap(f, g))
  def merge[A, B, C](f: A -> B, g: A -> C): A -> ⨂[B, C] = &&&(f, g)
  def merge3[A, B, C, D](f1: A -> B, f2: A -> C, f3: A -> D): A -> ⨂[B, ⨂[C, D]] = merge(f1, merge(f2, f3))
  def merge4[A, B, C, D, E](f1: A -> B, f2: A -> C, f3: A -> D, f4: A -> E): A -> ⨂[B, ⨂[C, ⨂[D, E]]] = merge(f1, merge(f2, merge(f3, f4)))


  def isoCartesian[A: TC, B: TC, C: TC]: (A -> B, A -> C) <=> (A -> ⨂[B, C]) =
    Iso.unsafe(&&&, fn => (C.andThen(fn, fst[B, C]), C.andThen(fn, snd[B, C])))

object Cartesian:
  type Aux [->[_,_], ⨂[_,_], T[_], I] = Cartesian[->, ⨂] { type TC[a] = T[a]; type Id = I }
  type AuxT[->[_,_], ⨂[_,_], T[_]]    = Cartesian[->, ⨂] { type TC[a] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: Cartesian[->, ⨂]): Cartesian.Aux[->, ⨂, c.TC, c.Id] = c

  trait Proto[->[_,_], ⨂[_,_], TC0[_], I] extends Cartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }
  
  extension[->[_,_], ⨁[_,_]](self: Cartesian[Dual[->,*,*], ⨁])
    def inl[A: self.TC, B: self.TC]: A -> ⨁[A, B] = self.fst
    def inr[A: self.TC, B: self.TC]: B -> ⨁[A, B] = self.snd
    def codiag[A: self.TC]: ⨁[A, A] -> A = self.diag
    def |||  [A, B, C](f: A -> C, g: B -> C): ⨁[A, B] -> C = self.&&&(Dual(f), Dual(g))
    def split[A, B, C](f: A -> C, g: B -> C): ⨁[A, B] -> C = |||(f, g)
    def split3[A, B, C, D](f1: A -> D, f2: B -> D, f3: C -> D): ⨁[A, ⨁[B, C]] -> D = |||(f1, |||(f2, f3))
    def split4[A, B, C, D, E](f1: A -> E, f2: B -> E, f3: C -> E, f4: D -> E): ⨁[A, ⨁[B, ⨁[C, D]]] -> E = |||(f1, |||(f2, |||(f3, f4)))
    def isoCocartesian[A: self.TC, B: self.TC, C: self.TC]: (A -> C, B -> C) <=> (⨁[A, B] -> C) =
      Iso.unsafe(
        |||,
        fn => (self.C.andThen(Dual(fn), self.fst[A, B]), self.C.andThen(Dual(fn), self.snd[A, B]))
      )
end Cartesian

type Cocartesian[->[_,_], ⨂[_,_]] = Cartesian[Dual[->, *, *], ⨂]
object Cocartesian:
  type Aux [->[_,_], ⨂[_,_], TC0[_], I] = Cocartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }
  type AuxT[->[_,_], ⨂[_,_], TC0[_]]    = Cocartesian[->, ⨂] { type TC[a] = TC0[a] }
  def apply[->[_,_], ⨂[_,_]](using c: Cartesian[Dual[->,*,*], ⨂]): Cartesian.Aux[Dual[->,*,*], ⨂, c.TC, c.Id] = c

trait CartesianK[->[_,_], ⨂[_,_]] extends MonoidalK[->, ⨂] with SymmetricK[->, ⨂]:
  def fst[F[_]: TC, G[_]: TC]: ∀[[a] =>> ⨂[F[a], G[a]] -> F[a]]
  def snd[F[_]: TC, G[_]: TC]: ∀[[a] =>> ⨂[F[a], G[a]] -> G[a]]
  def diag[F[_]: TC]: ∀[[a] =>> F[a] -> ⨂[F[a], F[a]]]

  def merge[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> F[a] -> H[a]]): ∀[[a] =>> F[a] -> ⨂[G[a], H[a]]] = &&&(f, g)
  def &&&  [F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> F[a] -> H[a]]): ∀[[a] =>> F[a] -> ⨂[G[a], H[a]]]

  def isoCartesian[F[_], G[_]: TC, H[_]: TC]: (∀[[a] =>> F[a] -> G[a]], ∀[[a] =>> F[a] -> H[a]]) <=> ∀[[a] =>> F[a] -> ⨂[G[a], H[a]]] =
    Iso.unsafe(
      &&&,
      fn => (C.andThen[F, [a] =>> G[a] ⨂ H[a], G](fn, fst[G, H]), C.andThen[F, [a] =>> G[a] ⨂ H[a], H](fn, snd[G, H]))
    )

object CartesianK:
  type Aux [->[_,_], ⨂[_,_], T[_[_]], I[_]] = CartesianK[->, ⨂] { type TC[a[_]] = T[a]; type Id[a] = I[a] }
  type AuxT[->[_,_], ⨂[_,_], T[_[_]]]       = CartesianK[->, ⨂] { type TC[a[_]] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: CartesianK[->, ⨂]): CartesianK.Aux[->, ⨂, c.TC, c.Id] = c

  trait Proto[->[_,_], ⨂[_,_], TC0[_[_]]] extends CartesianK[->, ⨂] { type TC[a[_]] = TC0[a] }

  extension[->[_,_], ⨁[_,_]](self: CocartesianK[->, ⨁])
    def inl[F[_]: self.TC, G[_]: self.TC]: ∀[[a] =>> F[a] -> ⨁[F[a], G[a]]] = ∀[[a] =>> F[a] -> ⨁[F[a], G[a]]](self.fst[F, G].apply)
    def inr[F[_]: self.TC, G[_]: self.TC]: ∀[[a] =>> G[a] -> ⨁[F[a], G[a]]] = ∀[[a] =>> G[a] -> ⨁[F[a], G[a]]](self.snd[F, G].apply)
    def codiag[F[_]: self.TC]: ∀[[a] =>> ⨁[F[a], F[a]] -> F[a]] = ∀[[a] =>> ⨁[F[a], F[a]] -> F[a]](self.diag[F].apply)
    def split[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> H[a]], g: ∀[[a] =>> G[a] -> H[a]]): ∀[[a] =>> ⨁[F[a], G[a]] -> H[a]] = |||(f, g)
    def |||  [F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> H[a]], g: ∀[[a] =>> G[a] -> H[a]]): ∀[[a] =>> ⨁[F[a], G[a]] -> H[a]] =
      ∀[[a] =>> ⨁[F[a], G[a]] -> H[a]](
        self.&&&(
          ∀[[a] =>> Dual[->, H[a], F[a]]](Dual(f.apply)),
          ∀[[a] =>> Dual[->, H[a], G[a]]](Dual(g.apply))
        ).apply
      )
    def isoCocartesian[F[_]: self.TC, G[_]: self.TC, H[_]]: (∀[[a] =>> F[a] -> H[a]], ∀[[a] =>> G[a] -> H[a]]) <=> ∀[[a] =>> ⨁[F[a], G[a]] -> H[a]] =
      Iso.unsafe(
        |||,
        fn => {
          val ff = ∀[[a] =>> Dual[->, H[a], F[a] ⨁ G[a]]](Dual(fn.apply))
          (
            ∀[[a] =>> F[a] -> H[a]](self.C.andThen[H, [a] =>> F[a] ⨁ G[a], F](ff, self.fst[F, G]).apply),
            ∀[[a] =>> G[a] -> H[a]](self.C.andThen[H, [a] =>> F[a] ⨁ G[a], G](ff, self.snd[F, G]).apply)
          )
        }
      )
end CartesianK

type CocartesianK[->[_,_], ⨂[_,_]] = CartesianK[Dual[->, *, *], ⨂]
object CocartesianK:
  type Aux [->[_,_], ⨂[_,_], T[_[_]], I[_]] = CocartesianK[->, ⨂] { type TC[a[_]] = T[a]; type Id[a] = I[a] }
  type AuxT[->[_,_], ⨂[_,_], T[_[_]]]       = CocartesianK[->, ⨂] { type TC[a[_]] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: CocartesianK[->, ⨂]): CocartesianK.Aux[->, ⨂, c.TC, c.Id] = c

trait CartesianK2[->[_,_], ⨂[_,_]] extends MonoidalK2[->, ⨂] with SymmetricK2[->, ⨂]:
  def fst[F[_,_]: TC, G[_,_]: TC]: ∀∀[[a, b] =>> ⨂[F[a, b], G[a, b]] -> F[a, b]]
  def snd[F[_,_]: TC, G[_,_]: TC]: ∀∀[[a, b] =>> ⨂[F[a, b], G[a, b]] -> G[a, b]]
  def diag[F[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] -> ⨂[F[a, b], F[a, b]]]

  def merge[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> F[a, b] -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> ⨂[G[a, b], H[a, b]]] = &&&(f, g)
  def &&&  [F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> F[a, b] -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> ⨂[G[a, b], H[a, b]]]

  def isoCartesian[F[_,_], G[_,_]: TC, H[_,_]: TC]: (∀∀[[a, b] =>> F[a, b] -> G[a, b]], ∀∀[[a, b] =>> F[a, b] -> H[a, b]]) <=> ∀∀[[a, b] =>> F[a, b] -> ⨂[G[a, b], H[a, b]]] =
    Iso.unsafe(
      &&&,
      fn => (C.andThen[F, [a, b] =>> G[a, b] ⨂ H[a, b], G](fn, fst[G, H]), C.andThen[F, [a, b] =>> G[a, b] ⨂ H[a, b], H](fn, snd[G, H]))
    )

object CartesianK2:
  type Aux [->[_,_], ⨂[_,_], T[_[_,_]], I[_,_]] = CartesianK2[->, ⨂] { type TC[a[_,_]] = T[a]; type Id[a, b] = I[a, b] }
  type AuxT[->[_,_], ⨂[_,_], T[_[_,_]]]         = CartesianK2[->, ⨂] { type TC[a[_,_]] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: CartesianK2[->, ⨂]): CartesianK2.Aux[->, ⨂, c.TC, c.Id] = c

  trait Proto[->[_,_], ⨂[_,_], TC0[_[_,_]]] extends CartesianK2[->, ⨂] { type TC[a[_,_]] = TC0[a] }

  extension[->[_,_], ⨁[_,_]](self: CocartesianK2[->, ⨁])
    def inl[F[_,_]: self.TC, G[_,_]: self.TC]: ∀∀[[a, b] =>> F[a, b] -> ⨁[F[a, b], G[a, b]]] = ∀∀[[a, b] =>> F[a, b] -> ⨁[F[a, b], G[a, b]]](self.fst[F, G].apply)
    def inr[F[_,_]: self.TC, G[_,_]: self.TC]: ∀∀[[a, b] =>> G[a, b] -> ⨁[F[a, b], G[a, b]]] = ∀∀[[a, b] =>> G[a, b] -> ⨁[F[a, b], G[a, b]]](self.snd[F, G].apply)
    def codiag[F[_,_]: self.TC]: ∀∀[[a, b] =>> ⨁[F[a, b], F[a, b]] -> F[a, b]] = ∀∀[[a, b] =>> ⨁[F[a, b], F[a, b]] -> F[a, b]](self.diag[F].apply)
    def split[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> H[a, b]], g: ∀∀[[a, b] =>> G[a, b] -> H[a, b]]): ∀∀[[a, b] =>> ⨁[F[a, b], G[a, b]] -> H[a, b]] = |||(f, g)
    def |||  [F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> H[a, b]], g: ∀∀[[a, b] =>> G[a, b] -> H[a, b]]): ∀∀[[a, b] =>> ⨁[F[a, b], G[a, b]] -> H[a, b]] =
      ∀∀[[a, b] =>> ⨁[F[a, b], G[a, b]] -> H[a, b]](
        self.&&&(
          ∀∀[[a, b] =>> Dual[->, H[a, b], F[a, b]]](Dual(f.apply)),
          ∀∀[[a, b] =>> Dual[->, H[a, b], G[a, b]]](Dual(g.apply))
        ).apply
      )
    def isoCocartesian[F[_,_]: self.TC, G[_,_]: self.TC, H[_,_]]: (∀∀[[a, b] =>> F[a, b] -> H[a, b]], ∀∀[[a, b] =>> G[a, b] -> H[a, b]]) <=> ∀∀[[a, b] =>> ⨁[F[a, b], G[a, b]] -> H[a, b]] =
      Iso.unsafe(
        |||,
        fn => {
          val ff = ∀∀[[a, b] =>> Dual[->, H[a, b], F[a, b] ⨁ G[a, b]]](Dual(fn.apply))
          (
            ∀∀[[a, b] =>> F[a, b] -> H[a, b]](self.C.andThen[H, [a, b] =>> F[a, b] ⨁ G[a, b], F](ff, self.fst[F, G]).apply),
            ∀∀[[a, b] =>> G[a, b] -> H[a, b]](self.C.andThen[H, [a, b] =>> F[a, b] ⨁ G[a, b], G](ff, self.snd[F, G]).apply)
          )
        }
      )
end CartesianK2

type CocartesianK2[->[_,_], ⨂[_,_]] = CartesianK2[Dual[->, *, *], ⨂]
object CocartesianK2:
  type Aux [->[_,_], ⨂[_,_], T[_[_,_]], I[_,_]] = CocartesianK2[->, ⨂] { type TC[a[_,_]] = T[a]; type Id[a, b] = I[a, b] }
  type AuxT[->[_,_], ⨂[_,_], T[_[_,_]]]         = CocartesianK2[->, ⨂] { type TC[a[_,_]] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: CocartesianK2[->, ⨂]): CocartesianK2.Aux[->, ⨂, c.TC, c.Id] = c

trait CartesianH[->[_,_], ⨂[_,_]] extends MonoidalH[->, ⨂] with SymmetricH[->, ⨂]:
  def fst[F[_[_]]: TC, G[_[_]]: TC]: ∀~[[a[_]] =>> ⨂[F[a], G[a]] -> F[a]]
  def snd[F[_[_]]: TC, G[_[_]]: TC]: ∀~[[a[_]] =>> ⨂[F[a], G[a]] -> G[a]]
  def diag[F[_[_]]: TC]: ∀~[[a[_]] =>> F[a] -> ⨂[F[a], F[a]]]

  def merge[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]], g: ∀~[[a[_]] =>> F[a] -> H[a]]): ∀~[[a[_]] =>> F[a] -> ⨂[G[a], H[a]]] = &&&(f, g)
  def &&&  [F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]], g: ∀~[[a[_]] =>> F[a] -> H[a]]): ∀~[[a[_]] =>> F[a] -> ⨂[G[a], H[a]]]

  def isoCartesian[F[_[_]], G[_[_]]: TC, H[_[_]]: TC]: (∀~[[a[_]] =>> F[a] -> G[a]], ∀~[[a[_]] =>> F[a] -> H[a]]) <=> ∀~[[a[_]] =>> F[a] -> ⨂[G[a], H[a]]] =
    Iso.unsafe(
      &&&,
      fn => (C.andThen[F, [a[_]] =>> G[a] ⨂ H[a], G](fn, fst[G, H]), C.andThen[F, [a[_]] =>> G[a] ⨂ H[a], H](fn, snd[G, H]))
    )

object CartesianH:
  type Aux [->[_,_], ⨂[_,_], T[_[_[_]]], I[_[_]]] = CartesianH[->, ⨂] { type TC[a[_[_]]] = T[a]; type Id[a[_]] = I[a] }
  type AuxT[->[_,_], ⨂[_,_], T[_[_[_]]]]          = CartesianH[->, ⨂] { type TC[a[_[_]]] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: CartesianH[->, ⨂]): CartesianH.Aux[->, ⨂, c.TC, c.Id] = c

  trait Proto[->[_,_], ⨂[_,_], TC0[_[_[_]]]] extends CartesianH[->, ⨂] { type TC[a[_[_]]] = TC0[a] }

  extension[->[_,_], ⨁[_,_]](self: CocartesianH[->, ⨁])
    def inl[F[_[_]]: self.TC, G[_[_]]: self.TC]: ∀~[[a[_]] =>> F[a] -> ⨁[F[a], G[a]]] = ∀~[[a[_]] =>> F[a] -> ⨁[F[a], G[a]]](self.fst[F, G].apply)
    def inr[F[_[_]]: self.TC, G[_[_]]: self.TC]: ∀~[[a[_]] =>> G[a] -> ⨁[F[a], G[a]]] = ∀~[[a[_]] =>> G[a] -> ⨁[F[a], G[a]]](self.snd[F, G].apply)
    def codiag[F[_[_]]: self.TC]: ∀~[[a[_]] =>> ⨁[F[a], F[a]] -> F[a]] = ∀~[[a[_]] =>> ⨁[F[a], F[a]] -> F[a]](self.diag[F].apply)
    def split[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> H[a]], g: ∀~[[a[_]] =>> G[a] -> H[a]]): ∀~[[a[_]] =>> ⨁[F[a], G[a]] -> H[a]] = |||(f, g)
    def |||  [F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> H[a]], g: ∀~[[a[_]] =>> G[a] -> H[a]]): ∀~[[a[_]] =>> ⨁[F[a], G[a]] -> H[a]] =
      ∀~[[a[_]] =>> ⨁[F[a], G[a]] -> H[a]](
        self.&&&(
          ∀~[[a[_]] =>> Dual[->, H[a], F[a]]](Dual(f.apply)),
          ∀~[[a[_]] =>> Dual[->, H[a], G[a]]](Dual(g.apply))
        ).apply
      )
    def isoCocartesian[F[_[_]]: self.TC, G[_[_]]: self.TC, H[_[_]]]: (∀~[[a[_]] =>> F[a] -> H[a]], ∀~[[a[_]] =>> G[a] -> H[a]]) <=> ∀~[[a[_]] =>> ⨁[F[a], G[a]] -> H[a]] =
      Iso.unsafe(
        |||,
        fn => {
          val ff = ∀~[[a[_]] =>> Dual[->, H[a], F[a] ⨁ G[a]]](Dual(fn.apply))
          (
            ∀~[[a[_]] =>> F[a] -> H[a]](self.C.andThen[H, [a[_]] =>> F[a] ⨁ G[a], F](ff, self.fst[F, G]).apply),
            ∀~[[a[_]] =>> G[a] -> H[a]](self.C.andThen[H, [a[_]] =>> F[a] ⨁ G[a], G](ff, self.snd[F, G]).apply)
          )
        }
      )
end CartesianH

type CocartesianH[->[_,_], ⨂[_,_]] = CartesianH[Dual[->, *, *], ⨂]
object CocartesianH:
  type Aux [->[_,_], ⨂[_,_], T[_[_[_]]], I[_[_]]] = CocartesianH[->, ⨂] { type TC[a[_[_]]] = T[a]; type Id[a[_]] = I[a] }
  type AuxT[->[_,_], ⨂[_,_], T[_[_[_]]]]          = CocartesianH[->, ⨂] { type TC[a[_[_]]] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: CocartesianH[->, ⨂]): CocartesianH.Aux[->, ⨂, c.TC, c.Id] = c
