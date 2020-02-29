package io.cosmo.exo

import io.cosmo.exo.categories.data.{KleisModule, KleisModuleImpl}
import io.cosmo.exo.categories.functors._

package object categories extends categories.syntax {


  val  Dual: DualModule    = DualImpl
  type Dual[->[_,_], A, B] = Dual.Dual[->, A, B]

  val  Kleis: KleisModule         = KleisModuleImpl
  type Kleis[->[_,_], F[_], A, B] = Kleis.Type[->, F, A, B]

  type Opp[->[_,_]] = {type l[A, B] = B -> A}

  type Cocartesian[->[_, _], ⨂[_, _]] = Cartesian[Opp[->]#l, ⨂]
  type Endofunctor[->[_,_], F[_]] = Exofunctor[->, ->, F]

  type Endobifunctor[->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]

}
