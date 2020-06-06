package io.cosmo.exo.categories

import cats.Id
import io.cosmo.exo._

package object functors {

  type Exo[==>[_,_], -->[_,_], F[_]] = Exofunctor[==>, -->, F]
  val Exo = Exofunctor

  type ExoRepr[==>[_,_], -->[_,_], F[_]] = ∃[λ[R => (Exofunctor[==>, -->, F], ∀[λ[x => Iso[==>, R --> x, F[x]]]])]]
  type Repr[->[_,_], F[_]] = ExoRepr[->, ->, F]

}
