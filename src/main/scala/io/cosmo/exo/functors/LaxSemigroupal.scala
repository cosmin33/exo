package io.cosmo.exo.functors

import io.cosmo.exo._
import io.cosmo.exo.categories._

trait LaxSemigroupal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] { self =>
  type TC[_]
  def A: Associative.Aux[-->, ⊙-, TC]
  def product[A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B]

  def map2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(using E: Exo[==>, -->, F]): (F[A] ⊙- F[B]) --> F[C] =
    A.C.andThen(product[A, B], E.map(fn))
  def comap2[==>[_,_], A, B, C](fn: C ==> (A ⊙= B))(using E: Exo[Dual[==>,*,*], -->, F]): (F[A] ⊙- F[B]) --> F[C] =
    A.C.andThen(product[A, B], E.map(Dual(fn)))

  def preserveCSemigroup[==>[_,_], M](ma: CSemigroup[==>, ⊙=, M])(using E: Exo[==>, -->, F]): CSemigroup[-->, ⊙-, F[M]] =
    CSemigroup.unsafe(map2(ma.op))(using A)

  def compose[~~>[_,_], ⊙~[_,_], G[_]](G: LaxSemigroupal[⊙-, ~~>, ⊙~, G])(using F: Exo[-->, ~~>, G]
  ): LaxSemigroupal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]] =
    new LaxSemigroupal[⊙=, ~~>, ⊙~, [a] =>> G[F[a]]] { type TC[a] = G.TC[a]; val A = G.A; def product[A, B] = G.map2(self.product[A, B]) }

}

object LaxSemigroupal extends LaxSemigroupalInstances {
  extension[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]](l: OplaxSemigroupal[⊙=, -->, ⊙-, F]) {
    def opProduct[A, B]: F[A ⊙= B] --> (F[A] ⊙- F[B]) = l.product[A, B]
    def opcomap2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(using
      C: Semicategory[-->], E: Exofunctor[==>, Dual[-->,*,*], F]
    ): F[C] --> (F[A] ⊙- F[B]) = l.map2(fn)
    def opmap2[==>[_,_], A, B, C](fn: C ==> (A ⊙= B))(using
      C: Semicategory[-->], E: Exofunctor[Dual[==>,*,*], Dual[-->,*,*], F]
    ): F[C] --> (F[A] ⊙- F[B]) = l.map2(Dual(fn))
  }
}

trait LaxSemigroupalInstances {
  // TODO: de facut
}