package io.cosmo.exo

import io.cosmo.exo.categories.functors._

package object categories extends categories.syntax {


  val Dual: DualModule = DualImpl
  type Dual[->[_,_], A, B] = Dual.Dual[->, A, B]

  type Opp[->[_,_]] = {type l[A, B] = B -> A}

  type Cocartesian[->[_, _], ⨂[_, _]] = Cartesian[Opp[->]#l, ⨂]
  type Endofunctor[->[_,_], F[_]] = Exofunctor[->, ->, F]

//  type Exobifunctor[==>[_,_], -->[_,_], ~~>[_,_], ⊙[_,_]] = InstanceOf[ExobifunctorClass[==>, -->, ~~>, ⊙]]
  type Endobifunctor[->[_,_], ⊙[_,_]] = Exobifunctor[->, ->, ->, ⊙]

}
