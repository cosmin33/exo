package io.cosmo.exo

import io.cosmo.exo
import io.cosmo.exo.categories.data.{KleisModule, KleisModuleImpl}
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.categories.instances.ProdcatInstances
import io.cosmo.exo.evidence.{===, =~~=}
import mouse.any._

package object categories extends ProdcatInstances with categories.syntax {

  type Tuple2Bi[B1[_,_], B2[_,_], A, B] = (B1[A, B], B2[A, B])

  /** alias for Tuple2Bi */
  type Prodcat[==>[_,_], -->[_,_], A, B] = (A ==> B, A --> B)
  object Prodcat {
    def traverseDualEq[==>[_,_], -->[_,_]]: Prodcat[Dual[==>,*,*], Dual[-->,*,*], *, *] =~~= Dual[Prodcat[==>,-->,*,*], *, *] =
      Dual.leibniz[==>].subst[λ[f[_,_] => Prodcat[f, Opp[-->]#l, *, *] =~~= Opp[Prodcat[==>,-->,*,*]]#l]](=~~=.refl) |>
        Dual.leibniz[-->].subst[λ[f[_,_] => Prodcat[Dual[==>,*,*], f, *, *] =~~= Opp[Prodcat[==>, -->, *, *]]#l]] |>
        Dual.leibniz[Prodcat[==>,-->,*,*]].subst
  }

  type Dicat[->[_,_], A, B] = (A -> B, Dual[->, A, B])
  object Dicat {
    def apply[->[_,_], A, B](to: A -> B, from: B -> A): Dicat[->, A, B] = (to, Dual(from))
  }

  val  Dual: DualModule    = DualImpl
  type Dual[->[_,_], A, B] = Dual.Dual[->, A, B]

  val  Kleis: KleisModule         = KleisModuleImpl
  type Kleis[->[_,_], F[_], A, B] = Kleis.Type[->, F, A, B]

  type Opp[->[_,_]] = {type l[A, B] = B -> A}

  type Cocartesian[->[_,_], ⨂[_,_]] = Cartesian[Dual[->, *, *], ⨂]
  type Endofunctor[->[_,_], F[_]] = Exofunctor[->, ->, F]

  type Endobifunctor[->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]
  type Endoprofunctor[->[_,_], ⊙[_,_]] = Exobifunctor[Dual[->,*,*], ->, ->, ⊙]

}
