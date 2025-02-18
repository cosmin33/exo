package io.cosmo.exo.categories

import io.cosmo.exo
import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.any.*
import io.cosmo.exo.syntax.*

type Prodcat[==>[_,_], -->[_,_], A, B] = (A ==> B, A --> B)
object Prodcat:
  /** Product category of duals is the same as dual of product category */
  def traverseDualEq[==>[_,_], -->[_,_]]: Prodcat[Dual[==>,*,*], Dual[-->,*,*],*,*] =~~= Dual[Prodcat[==>, -->,*,*],*,*] =
    Dual.leibniz[==>].subst[[f[_,_]] =>> Prodcat[f, Opp[-->],*,*] =~~= Opp[Prodcat[==>, -->,*,*]]](=~~=.refl) |>
      Dual.leibniz[-->].subst[[f[_,_]] =>> Prodcat[Dual[==>,*,*], f,*,*] =~~= Opp[Prodcat[==>, -->,*,*]]] |>
      Dual.leibniz[Prodcat[==>, -->,*,*]].subst

type Opp[->[_,_]] = [a,b] =>> b -> a

type Dicat[->[_,_], A, B] = (A -> B, Dual[->, A, B])
object Dicat:
  def apply[->[_,_], A, B](to: A -> B, from: B -> A): Dicat[->, A, B] = (to, Dual(from))
  def unsafeIsoIso[->[_,_]](using C: Semicategory[->]): Dicat[->,*,*] <~~> Iso[->,*,*] =
    IsoK2.unsafe(
      ∀∀[[a,b] =>> Dicat[->, a, b] => Iso[->, a, b]](d => Iso.unsafe(d._1, d._2)),
      ∀∀[[a,b] =>> Iso[->, a, b] => Dicat[->, a, b]](i => (i.to, i.from.dual))
    )
