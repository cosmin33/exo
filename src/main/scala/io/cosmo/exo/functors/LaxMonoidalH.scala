package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

trait LaxMonoidalH[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_[_]]]] extends LaxSemigroupalH[⊙=, -->, ⊙-, A]:
  type I
  def A: Monoidal.Aux[-->, ⊙-, TC, I]
  def id: I --> A[[a[_]] =>> I]

  def preserveCMonoid[==>[_,_], TC2[_], M[_[_]]](ma: CMonoidH.Aux[==>, ⊙=, M, [a[_]] =>> I])(using
    E: ExoH[==>, -->, A]
  ): CMonoid.Aux[-->, ⊙-, A[M], I] =
    CMonoid.unsafe(A.C.andThen(id, E.map(ma.id)), map2(ma.op))(using A)

object LaxMonoidalH:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, A[_[_[_]]]] = LaxMonoidalH[⊙=, -->, ⊙-, A] { type TC[a] = C[a]; type I = I0 }

  trait Proto[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, A[_[_[_]]]] extends LaxMonoidalH[⊙=, -->, ⊙-, A]:
    type TC[a] = C[a]
    type I = I0