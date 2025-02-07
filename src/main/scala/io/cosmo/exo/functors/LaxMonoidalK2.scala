package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*

trait LaxMonoidalK2[⊙=[_,_], -->[_,_], ⊙-[_,_], A[_[_,_]]] extends LaxSemigroupalK2[⊙=, -->, ⊙-, A]:
  type I
  def A: Monoidal.Aux[-->, ⊙-, TC, I]
  def id: I --> A[[a,b] =>> I]
  
  def preserveCMonoid[==>[_,_], TC2[_], M[_,_]](ma: CMonoidK2.Aux[==>, ⊙=, M, [a,b] =>> I])(using
    E: ExoK2[==>, -->, A]
  ): CMonoid.Aux[-->, ⊙-, A[M], I] =
    CMonoid.unsafe(A.C.andThen(id, E.map(ma.id)), map2(ma.op))(using A)

object LaxMonoidalK2:
  type Aux[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, A[_[_,_]]] = LaxMonoidalK2[⊙=, -->, ⊙-, A] { type TC[a] = C[a]; type I = I0 }
  
  trait Proto[⊙=[_,_], -->[_,_], ⊙-[_,_], C[_], I0, A[_[_,_]]] extends LaxMonoidalK2[⊙=, -->, ⊙-, A]:
    type TC[a] = C[a]
    type I = I0
