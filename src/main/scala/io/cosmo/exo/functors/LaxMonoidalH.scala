package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

trait LaxMonoidalH[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_[_]]]] extends LaxSemigroupalH[⊙=, -->, ⊙-, A]:
  type I
  def A: Monoidal.Aux[-->, ⊙-, TC, I]
  def id[F[_[_]]]: I --> A[F]

  def preserveCMonoid[==>[_,_], TC2[_], M[_[_]]](ma: CMonoidH[==>, ⊙=, M])(using
    E: ExoH[==>, -->, A]
  ): CMonoid.Aux[-->, ⊙-, A[M], I] =
    CMonoid.unsafe(A.C.andThen(id[ma.I], E.map(ma.id)), map2(ma.op))(using A)

object LaxMonoidalH:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, A[_[_[_]]]] = LaxMonoidalH[⊙=, -->, ⊙-, A] { type TC[a] = C[a]; type I = I0 }
