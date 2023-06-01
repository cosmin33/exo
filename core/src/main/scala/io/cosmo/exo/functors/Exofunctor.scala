package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

trait Exofunctor[==>[_,_], -->[_,_], F[_]]:
  self =>

  def map[A, B](f: A ==> B): F[A] --> F[B]

  final def compose[>->[_,_], G[_]](G: Exo[>->, ==>, G]): Exofunctor[>->, -->, [α] =>> F[G[α]]] =
    Exo.unsafe([a, b] => (f: a >-> b) => self.map(G.map(f)))

end Exofunctor

object Exofunctor:
  def apply[==>[_,_], -->[_,_], F[_]](using F: Exofunctor[==>, -->, F]): Exofunctor[==>, -->, F] = F

  def unsafe[==>[_,_], -->[_,_], F[_]](fn: [a, b] => (a ==> b) => (F[a] --> F[b])): Exofunctor[==>, -->, F] =
    new Exofunctor[==>, -->, F]:
      def map[A, B](f: A ==> B): F[A] --> F[B] = fn[A, B](f)

  type Cov[->[_,_], F[_]] = Exo[->, Function, F]
  object Cov:
    def apply[->[_, _], F[_]](using E: Cov[->, F]): Cov[->, F] = E
  /** This is isomorphic to cats Functor */
  type CovF[F[_]] = Exo[Function, Function, F]
  object CovF:
    def apply[F[_]](implicit E: CovF[F]): CovF[F] = E

  type Con[->[_, _], F[_]] = Exo[Dual[->, *, *], * => *, F]
  object Con:
    def apply[->[_, _], F[_]](using E: Con[->, F]): Con[->, F] = E
  /** This is isomorphic to cats Contravariant */
  type ConF[F[_]] = Con[Function, F]
  object ConF:
    def apply[F[_]](using E: ConF[F]): ConF[F] = E

  type Inv[->[_, _], F[_]] = Exo[Dicat[->, *, *], Function, F]
  object Inv:
    def apply[->[_, _], F[_]](using E: Inv[->, F]): Inv[->, F] = E
  /** This is isomorphic to cats Invariant */
  type InvF[F[_]] = Inv[Function, F]
  object InvF:
    def apply[F[_]](using E: InvF[F]): InvF[F] = E

  /** Exofunctor from an isomorphism category to Function1 */
  type IsoFun[->[_,_], F[_]] = Exo[Iso[->,_,_], Function, F]
  object IsoFun:
    def apply[->[_, _], F[_]](using E: IsoFun[->, F]): IsoFun[->, F] = E

//  /** Exofunctor from an isomorphism in a category to iso of function1 */
//  type IsoIso[->[_, _], F[_]] = Exo[Iso[->, *, *], Iso[Function, *, *], F]

end Exofunctor
