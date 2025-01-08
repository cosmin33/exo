package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

trait LaxMonoidalK[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_]]] extends LaxSemigroupalK[⊙=, -->, ⊙-, A]:
  type I
  def A: Monoidal.Aux[-->, ⊙-, TC, I]
  def id[F[_]]: I --> A[F]

  def preserveCMonoid[==>[_,_], TC2[_], M[_]](ma: CMonoidK[==>, ⊙=, M])(using
    E: ExoK[==>, -->, A]
  ): CMonoid.Aux[-->, ⊙-, A[M], I] =
    CMonoid.unsafe(A.C.andThen(id[ma.I], E.map(ma.id)), map2(ma.op))(using A)

object LaxMonoidalK:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, A[_[_]]] = LaxMonoidalK[⊙=, -->, ⊙-, A] { type TC[a] = C[a]; type I = I0 }
