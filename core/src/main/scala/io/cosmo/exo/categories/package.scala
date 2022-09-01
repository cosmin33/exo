package io.cosmo.exo

import io.cosmo.exo.categories.data.{KleisModule, KleisModuleImpl}
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.categories.instances.ProdcatInstances
import io.cosmo.exo.evidence.{===, =~~=}
import io.cosmo.exo.internal.any._

package object categories extends ProdcatInstances with categories.syntax {

  type Prodcat_1[==>[_,_], -->[_,_], A, B] = A ==> B
  type Prodcat_2[==>[_,_], -->[_,_], A, B] = A --> B
  type Prodcat[==>[_,_], -->[_,_], A, B] = (A ==> B, A --> B)
  object Prodcat {
    /** Product category of duals is the same as dual of product category */
    def traverseDualEq[==>[_,_], -->[_,_]]: Prodcat[Dual[==>,*,*], Dual[-->,*,*], *, *] =~~= Dual[Prodcat[==>,-->,*,*], *, *] =
      Dual.leibniz[==>].subst[λ[f[_,_] => Prodcat[f, Opp[-->]#l, *, *] =~~= Opp[Prodcat[==>,-->,*,*]]#l]](=~~=.refl) |>
        Dual.leibniz[-->].subst[λ[f[_,_] => Prodcat[Dual[==>,*,*], f, *, *] =~~= Opp[Prodcat[==>, -->, *, *]]#l]] |>
        Dual.leibniz[Prodcat[==>,-->,*,*]].subst
  }
  private def proof1[==>[_,_], -->[_,_], A, B] =
    implicitly[Prodcat[==>, -->, A, B] === (Prodcat_1[==>, -->, A, B], Prodcat_2[==>, -->, A, B])]
  
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
  type Exomonad1[->[_,_], TC[_], F[_]] = Subcat.Aux[λ[(a,b) => a -> F[b]], TC] /\ Exo[λ[(a,b) => a -> F[b]], ->, F]

  type Endobifunctor [->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]
  type Endoprofunctor[->[_,_], ⊙[_,_]] = Exobifunctor[Dual[->,*,*], ->, ->, ⊙]

  type CSemigroupK[->[_,_], ⊙[_,_], F[_]] = ∀[λ[a => CSemigroup[->, ⊙, F[a]]]]
  type CMonoidK   [->[_,_], ⊙[_,_], F[_]] = ∀[λ[a => CMonoid   [->, ⊙, F[a]]]]

  type Exorepresentable[->[_,_], F[_], Repr] = Exo.Cov[->, F] /\ (F <~> (Repr -> *))

}
