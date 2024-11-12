package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

trait Cartesian[->[_,_], ⨂[_,_]] extends Monoidal[->, ⨂] with Symmetric[->, ⨂] {
  def fst[A: TC, B: TC]: ⨂[A, B] -> A
  def snd[A: TC, B: TC]: ⨂[A, B] -> B
  def diag[A: TC]: A -> ⨂[A, A]

  def merge[A, B, C](f: A -> B, g: A -> C): A -> ⨂[B, C] = &&&(f, g)
  def &&&  [A, B, C](f: A -> B, g: A -> C): A -> ⨂[B, C]
  //def &&&  [X: TC, Y, Z](f: X -> Y, g: X -> Z): X -> ⨂[Y, Z] = C.andThen(diag[X], bifunctor.bimap(f, g))

  def isoCartesian[A, B: TC, C: TC]: (A -> B, A -> C) <=> (A -> ⨂[B, C]) =
    Iso.unsafe(&&&, fn => (C.andThen(fn, fst[B, C]), C.andThen(fn, snd[B, C])))
}

object Cartesian {
  type Aux[->[_,_], ⨂[_,_], T[_], I] = Cartesian[->, ⨂] { type TC[a] = T[a]; type Id = I }
  type AuxT[->[_,_], ⨂[_,_], T[_]] = Cartesian[->, ⨂] { type TC[a] = T[a] }
  def apply[->[_,_], ⨂[_,_]](using c: Cartesian[->, ⨂]): Cartesian.Aux[->, ⨂, c.TC, c.Id] = c

  trait Proto[->[_,_], ⨂[_,_], TC0[_], I] extends Cartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }
  
  extension[->[_,_], ⨁[_,_]](self: Cartesian[Dual[->,*,*], ⨁])
    def inl[A: self.TC, B: self.TC]: A -> ⨁[A, B] = self.fst
    def inr[A: self.TC, B: self.TC]: B -> ⨁[A, B] = self.snd
    def codiag[A: self.TC]: ⨁[A, A] -> A = self.diag
    def split[A, B, C](f: A -> C, g: B -> C): ⨁[A, B] -> C = |||(f, g)
    def |||  [A, B, C](f: A -> C, g: B -> C): ⨁[A, B] -> C = self.&&&(Dual(f), Dual(g))
    def isoCocartesian[A: self.TC, B: self.TC, C]: (A -> C, B -> C) <=> (⨁[A, B] -> C) =
      Iso.unsafe(
        p => |||(p._1, p._2),
        fn => (self.C.andThen(Dual(fn), self.fst[A, B]), self.C.andThen(Dual(fn), self.snd[A, B]))
      )

  extension[->[_,_], ⨂[_,_], I[_]](a: CartesianK.Aux[->, ⨂, I])
    def fstK[F[_], G[_]](using IsInjective2[⨂]): ∀[[a] =>> ⨂[F[a], G[a]] -> F[a]] =
      a.fst[TypeK[F], TypeK[G]].unapply
    def sndK[F[_], G[_]](using IsInjective2[⨂]): ∀[[a] =>> ⨂[F[a], G[a]] -> G[a]] =
      a.snd[TypeK[F], TypeK[G]].unapply
    def diagK[F[_]](using IsInjective2[⨂]): ∀[[a] =>> F[a] -> ⨂[F[a], F[a]]] =
      a.diag[TypeK[F]].unapply
    def mergeK[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> F[a] -> H[a]])(using IsInjective2[⨂])
    : ∀[[a] =>> F[a] -> ⨂[G[a], H[a]]] =
      a.merge[TypeK[F], TypeK[G], TypeK[H]](ArrowK(f), ArrowK(g)).unapply
    def isoCartesianK[F[_], G[_], H[_]](using IsInjective2[⨂], Subcat[->])
    : (∀[[a] =>> F[a] -> G[a]], ∀[[a] =>> F[a] -> H[a]]) <=> ∀[[a] =>> F[a] -> ⨂[G[a], H[a]]] =
      val i = a.isoCartesian[TypeK[F], TypeK[G], TypeK[H]]
      Iso.unsafe(
        p => i.to((ArrowK(p._1), ArrowK(p._2))).unapply,
        fn => {
          val ikgh: IsKind.Aux[TypeK[G] ⨂ TypeK[H], [a] =>> G[a] ⨂ H[a]] = IsKind.pairInjectivity[⨂, TypeK[G], TypeK[H]]
          val f1 = ArrowK[->, TypeK[F], TypeK[G] ⨂ TypeK[H], F, [a] =>> G[a] ⨂ H[a]](fn)(using summon, ikgh)
          val (afg, afh) = i.from(f1)
          (afg.unapply, afh.unapply)
        }
      )

  extension[->[_,_], ⨁[_,_], I[_]](a: CocartesianK.Aux[->, ⨁, I])
    def inlK[F[_], G[_]](using IsInjective2[⨁]): ∀[[a] =>> F[a] -> ⨁[F[a], G[a]]] =
      a.inl[TypeK[F], TypeK[G]].unapply
    def inrK[F[_], G[_]](using IsInjective2[⨁]): ∀[[a] =>> G[a] -> ⨁[F[a], G[a]]] =
      a.inr[TypeK[F], TypeK[G]].unapply
    def codiagK[F[_]](using IsInjective2[⨁]): ∀[[a] =>> ⨁[F[a], F[a]] -> F[a]] =
      a.codiag[TypeK[F]].unapply
    def splitK[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> H[a]], g: ∀[[a] =>> G[a] -> H[a]])(using IsInjective2[⨁])
    : ∀[[a] =>> ⨁[F[a], G[a]] -> H[a]] =
      a.split[TypeK[F], TypeK[G], TypeK[H]](ArrowK(f), ArrowK(g)).unapply
    def isoCocartesianK[F[_], G[_], H[_]](using IsInjective2[⨁], Subcat[->])
    : (∀[[a] =>> F[a] -> H[a]], ∀[[a] =>> G[a] -> H[a]]) <=> ∀[[a] =>> ⨁[F[a], G[a]] -> H[a]] =
      val i = a.isoCocartesian[TypeK[F], TypeK[G], TypeK[H]]
      Iso.unsafe(
        p => i.to((ArrowK(p._1), ArrowK(p._2))).unapply,
        fn => {
          val ikfg: IsKind.Aux[TypeK[F] ⨁ TypeK[G], [a] =>> F[a] ⨁ G[a]] = IsKind.pairInjectivity[⨁, TypeK[F], TypeK[G]]
          val f1 = ArrowK[->, TypeK[F] ⨁ TypeK[G], TypeK[H], [a] =>> F[a] ⨁ G[a], H](fn)(using ikfg, summon)
          val (afh, agh) = i.from(f1)
          (afh.unapply, agh.unapply)
        }
      )

}

type Cocartesian[->[_,_], ⨂[_,_]] = Cartesian[Dual[->, *, *], ⨂]
object Cocartesian {
  type Aux[->[_,_], ⨂[_,_], TC0[_], I] = Cocartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }
  type AuxT[->[_,_], ⨂[_,_], TC0[_]] = Cocartesian[->, ⨂] { type TC[a] = TC0[a] }
  def apply[->[_,_], ⨂[_,_]](using c: Cartesian[Dual[->,*,*], ⨂]): Cartesian.Aux[Dual[->,*,*], ⨂, c.TC, c.Id] = c
}
