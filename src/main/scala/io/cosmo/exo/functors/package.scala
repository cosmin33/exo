package io.cosmo.exo.functors

import io.cosmo.exo.categories._

type Exo[==>[_, _], -->[_, _], F[_]] = Exofunctor[==>, -->, F]
val Exo = Exofunctor

type Endofunctor[->[_,_], F[_]] = Exofunctor[->, ->, F]
object Endofunctor:
  /** This is isomorphic to cats.Functor[F] */
  type CovF[F[_]] = Endofunctor[* => *, F]

  def apply[->[_,_], F[_]](using E: Endofunctor[->, F]): Endofunctor[->, F] = E
  def unsafe[->[_,_], F[_]](fn: [a, b] => (a -> b) => (F[a] -> F[b])): Endofunctor[->, F] = Exofunctor.unsafe(fn)


type Endobifunctor[->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]
type Exoprofunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]] = Exobifunctor[Dual[==>,*,*], -->, >->, ⊙]
type Endoprofunctor[->[_,_], ⊙[_,_]] = Exobifunctor[Dual[->, *, *], ->, ->, ⊙]

type OplaxSemigroupal[=⊙[_, _], -->[_, _], -⊙[_, _], F[_]] = LaxSemigroupal[=⊙, Dual[-->, *, *], -⊙, F]
type OplaxMonoidal   [=⊙[_, _], -->[_, _], -⊙[_, _], F[_]] = LaxMonoidal   [=⊙, Dual[-->, *, *], -⊙, F]
