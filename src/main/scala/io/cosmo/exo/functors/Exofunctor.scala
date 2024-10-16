package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.syntax.*

trait Exofunctor[==>[_,_], -->[_,_], F[_]] { self =>

  def map[A, B](f: A ==> B): F[A] --> F[B]

  final def compose[>->[_,_], G[_]](G: Exo[-->, >->, G]): Exofunctor[==>, >->, [α] =>> G[F[α]]] =
    Exo.unsafe([a, b] => (f: a ==> b) => G.map(self.map(f)))
}

object Exofunctor extends ExofunctorInstances {
  def apply[==>[_,_], -->[_,_], F[_]](using F: Exofunctor[==>, -->, F]): Exofunctor[==>, -->, F] = F

  def unsafe[==>[_,_], -->[_,_], F[_]](fn: [a, b] => (a ==> b) => (F[a] --> F[b])): Exofunctor[==>, -->, F] =
    new Exofunctor[==>, -->, F]:
      def map[A, B](f: A ==> B): F[A] --> F[B] = fn[A, B](f)

  type Cov[->[_,_], F[_]] = Exo[->, Function, F]
  object Cov:
    def apply[->[_,_], F[_]](using E: Cov[->, F]): Cov[->, F] = E

  /** This is isomorphic to cats Functor */
  type CovF[F[_]] = Exo[Function, Function, F]
  object CovF:
    def apply[F[_]](using E: CovF[F]): CovF[F] = E

  type Con[->[_,_], F[_]] = Exo[Dual[->, *, *], * => *, F]
  object Con:
    def apply[->[_,_], F[_]](using E: Con[->, F]): Con[->, F] = E

  /** This is isomorphic to cats Contravariant */
  type ConF[F[_]] = Con[Function, F]
  object ConF:
    def apply[F[_]](using E: ConF[F]): ConF[F] = E

  type Inv[->[_,_], F[_]] = Exo[Dicat[->, *, *], Function, F]
  object Inv:
    def apply[->[_,_], F[_]](using E: Inv[->, F]): Inv[->, F] = E

  /** This is isomorphic to cats Invariant */
  type InvF[F[_]] = Inv[Function, F]
  object InvF:
    def apply[F[_]](using E: InvF[F]): InvF[F] = E

  /** Exofunctor from an isomorphism category to Function1 */
  type IsoFun[->[_,_], F[_]] = Exo[Iso[->,_,_], Function, F]
  object IsoFun:
    def apply[->[_,_], F[_]](using E: IsoFun[->, F]): IsoFun[->, F] = E

  // extension methods for higher kinded functors
  extension [H[_[_]]](self: FunctorK[H])
    def mapK[F[_], G[_]](f: F ~> G): H[F] => H[G] = self.map(FunK(f)).isoTo

  extension[H[_[_]]](self: CofunctorK[H])
    def comapK[F[_], G[_]](f: G ~> F): H[F] => H[G] = self.map(Dual(FunK(f))).isoTo

  extension[H[_[_]]](self: IsoFunctorK[H])
    def isoMapK[F[_], G[_]](f: F <~> G): H[F] <=> H[G] = self.map(IsoFunK(f)).isoTo

  extension[H[_[_,_]]](self: FunctorK2[H])
    def mapK2[F[_,_], G[_,_]](f: F ~~> G): H[F] => H[G] = self.map(FunK2(f)).isoTo

  extension[H[_[_,_]]](self: CofunctorK2[H])
    def comapK2[F[_,_], G[_,_]](f: G ~~> F): H[F] => H[G] = self.map(Dual(FunK2(f))).isoTo

  extension[H[_[_,_]]](self: IsoFunctorK2[H])
    def isoMapK2[F[_,_], G[_,_]](f: F <~~> G): H[F] <=> H[G] = self.map(IsoFunK2(f)).isoTo
}

trait ExofunctorInstances extends ExofunctorInstances01 {
  given idEndofunctor[->[_,_]]: Endofunctor[->, [a] =>> a] = Endofunctor.unsafe[->, [a] =>> a]([a, b] => (f: a -> b) => f)

  /** from semicategory to left and right functors */
  given semiFunctorCov[->[_,_] : Semicategory, X]: Exo.Cov[->, ->[X,*]] =
    Exo.unsafe([a, b] => (f: a -> b) => (fn: X -> a) => fn >>> f)

  given semiFunctorCon[->[_,_] : Semicategory, X]: Exo.Con[->, ->[*,X]] =
    Exo.unsafe[Dual[->,*,*], * => *, [o] =>> o -> X]([a, b] => (f: Dual[->, a, b]) => (fn: a -> X) => f.toFn >>> fn)

  given mapLeibnizLiskov [->[_,_], F[_]](using F: Exo[->, ===, F]): Exo[->, <~<, F] =
    Exo.unsafe[->, <~<, F]([a, b] => (f: a -> b) => F.map(f).toAs)
  given mapLeibnizLiskov1[->[_,_], F[_]](using F: Exo[->, ===, F]): Exo[->, >~>, F] =
    Exo.unsafe[->, >~>, F]([a, b] => (f: a -> b) => F.map(f).flip.toAs)
  given mapLeibnizIso    [->[_,_], F[_]](using F: Exo[->, ===, F]): Exo[->, <=>, F] =
    Exo.unsafe[->, <=>, F]([a, b] => (f: a -> b) => F.map(f).toIso)
  given mapLiskovFunction[->[_,_], F[_]](using F: Exo[->, <~<, F]): Exo[->, * => *, F] =
    Exo.unsafe[->, * => *, F]([a, b] => (f: a -> b) => F.map(f).apply(_))
}

trait ExofunctorInstances01 extends ExofunctorInstances02 {
  given mapIsoTo[-->[_,_], ==>[_,_], F[_]](using F: Exo[-->, Iso[==>,*,*], F]): Exo[-->, ==>, F] =
    Exo.unsafe[-->, ==>, F]([a, b] => (f: a --> b) => F.map(f).to)
}

trait ExofunctorInstances02 {
  given groupoidComap[==>[_,_], -->[_,_], F[_]](using F: Exo[==>, -->, F], G: Groupoid[==>]): Exo[Dual[==>, *, *], -->, F] =
    Exo.unsafe[Dual[==>,*,*], -->, F]([a, b] => (f: Dual[==>, a, b]) => F.map(G.flip(f)))

  given groupoidMap[==>[_,_], -->[_,_], F[_]](using F: Exo[==>, -->, F], G: Groupoid[-->]): Exo[==>, Dual[-->, *, *], F] =
    Exo.unsafe[==>, Dual[-->,*,*], F]([a, b] => (f: a ==> b) => Dual(G.flip(F.map(f))))
}
