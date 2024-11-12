package io.cosmo.exo.categories

import io.cosmo.exo.evidence.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.internal.*

opaque type Dual[->[_,_], A, B] <: B -> A = B -> A

object Dual:
  
  def apply[->[_,_], A, B](f: B -> A): Dual[->, A, B] = f
  def leibniz[->[_,_]]: Opp[->] =~~= Dual[->,*,*] = IsK2.refl
  def is[->[_, _], A, B]: (B -> A) === Dual[->, A, B] = leibniz[->].is[A, B]

  extension [->[_,_], A, B](self: Dual[->, A, B])
    def toFn: B -> A = self
  
  given nestedDualCancelsItself[->[_,_]]: (Dual[Dual[->,*,*],*,*] =~~= ->) =
    Dual.leibniz[->].subst[[f[_,_]] =>> Opp[Opp[->]] =~~= Dual[f, *, *]](Dual.leibniz[Opp[->]]).flip
  
end Dual
