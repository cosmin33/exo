package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

trait LaxSemigroupal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]]:
  self =>
  type TD[_]
  def D: Associative.Aux[-->, ⊙-, TD]
  def product[A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B]

  def map2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(using E: Exo[==>, -->, F]): (F[A] ⊙- F[B]) --> F[C] =
    D.C.andThen(product[A, B], E.map(fn))
  def comap2[==>[_,_], A, B, C](fn: C ==> (A ⊙= B))(using E: Exo[Dual[==>,*,*], -->, F]): (F[A] ⊙- F[B]) --> F[C] =
    D.C.andThen(product[A, B], E.map(Dual(fn)))

  def preserveCSemigroup[==>[_,_], M](ma: CSemigroup[==>, ⊙=, M])(using E: Exo[==>, -->, F]): CSemigroup[-->, ⊙-, F[M]] =
    CSemigroup.unsafe(map2(ma.op))(using D)

  def compose[~~>[_,_], ⊙~[_,_], G[_]](G: LaxSemigroupal[⊙-, ~~>, ⊙~, G])(using F: Exo[-->, ~~>, G]
  ): LaxSemigroupal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]] =
    new LaxSemigroupal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]]:
      type TD[a] = G.TD[a]; val D = G.D; def product[A, B] = G.map2(self.product[A, B])

object LaxSemigroupal extends LaxSemigroupalInstances:
  def apply[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](using l: LaxSemigroupal[⊙=, -->, ⊙-, F]): LaxSemigroupal[⊙=, -->, ⊙-, F] = l
  extension[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](l: OplaxSemigroupal[⊙=, -->, ⊙-, F])
    def opProduct[A, B]: F[A ⊙= B] --> (F[A] ⊙- F[B]) = l.product[A, B]
    def opcomap2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(using
      Semicategory[-->], Exofunctor[==>, Dual[-->,*,*], F]
    ): F[C] --> (F[A] ⊙- F[B]) = l.map2(fn)
    def opmap2[==>[_,_], A, B, C](fn: C ==> (A ⊙= B))(using 
      Semicategory[-->], Exofunctor[Dual[==>,*,*], Dual[-->,*,*], F]
    ): F[C] --> (F[A] ⊙- F[B]) = l.map2(Dual(fn))

private[exo] trait LaxSemigroupalInstances {
  // TODO: de facut
}
