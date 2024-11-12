package io.cosmo.exo.categories

import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.any.*
import io.cosmo.exo.*

type Prodcat[==>[_,_], -->[_,_], A, B] = (A ==> B, A --> B)
object Prodcat:
  /** Product category of duals is the same as dual of product category */
  def traverseDualEq[==>[_, _], -->[_, _]]: Prodcat[Dual[==>, *, *], Dual[-->, *, *], *, *] =~~= Dual[Prodcat[==>, -->, *, *], *, *] =
    Dual.leibniz[==>].subst[[f[_,_]] =>> Prodcat[f, Opp[-->], *, *] =~~= Opp[Prodcat[==>, -->, *, *]]](=~~=.refl) |>
      Dual.leibniz[-->].subst[[f[_,_]] =>> Prodcat[Dual[==>, *, *], f, *, *] =~~= Opp[Prodcat[==>, -->, *, *]]] |>
      Dual.leibniz[Prodcat[==>, -->, *, *]].subst

type Opp[->[_,_]] = [a,b] =>> b -> a

type Dicat[->[_,_], A, B] = (A -> B, Dual[->, A, B])
object Dicat:
  def apply[->[_,_], A, B](to: A -> B, from: B -> A): Dicat[->, A, B] = (to, Dual(from))

/////////////////////////////////////////////
// Categories for kinds
/////////////////////////////////////////////

type AssociativeK[->[_,_], ⊙[_,_]] = Associative.Aux[ArrowK[->, *, *], ⊙, IsKind]
type CoAssociativeK[->[_,_], ⊙[_,_]] = Associative.Aux[Dual[ArrowK[->, *, *], *, *], ⊙, IsKind]

type BraidedK[->[_,_], ⊙[_,_]] = Braided.Aux[ArrowK[->, *, *], ⊙, IsKind]
type CoBraidedK[->[_,_], ⊙[_,_]] = Braided.Aux[Dual[ArrowK[->, *, *], *, *], ⊙, IsKind]

type SymmetricK[->[_,_], ⊙[_,_]] = Symmetric.Aux[ArrowK[->, *, *], ⊙, IsKind]
type CoSymmetricK[->[_,_], ⊙[_,_]] = Symmetric.Aux[Dual[ArrowK[->, *, *], *, *], ⊙, IsKind]

type MonoidalK[->[_,_], ⊙[_,_]] = Monoidal[ArrowK[->, *, *], ⊙] { type TC[a] = IsKind[a] }
object MonoidalK:
  type Aux[->[_,_], ⊙[_,_], I[_]] = Monoidal.Aux[ArrowK[->, *, *], ⊙, IsKind, TypeK[I]]
type CoMonoidalK[->[_,_], ⊙[_,_]] = Monoidal[Dual[ArrowK[->, *, *], *, *], ⊙] { type TC[a] = IsKind[a] }
object CoMonoidalK:
  type Aux[->[_,_], ⊙[_,_], I[_]] = Monoidal.Aux[Dual[ArrowK[->, *, *], *, *], ⊙, IsKind, TypeK[I]]

type CartesianK[->[_,_], ⊙[_,_]] = Cartesian[ArrowK[->, *, *], ⊙] { type TC[a] = IsKind[a] }
object CartesianK:
  type Aux[->[_,_], ⊙[_,_], I[_]] = Cartesian.Aux[ArrowK[->, *, *], ⊙, IsKind, TypeK[I]]
type CocartesianK[->[_,_], ⊙[_,_]] = Cartesian[Dual[ArrowK[->, *, *], *, *], ⊙] { type TC[a] = IsKind[a] }
object CocartesianK:
  type Aux[->[_,_], ⊙[_,_], I[_]] = Cartesian.Aux[Dual[ArrowK[->, *, *], *, *], ⊙, IsKind, TypeK[I]]

type CccK[->[_,_], ⊙[_,_]] = Ccc[ArrowK[->, *, *], ⊙, ->] { type TC[a] = IsKind[a] }
object CccK:
  type Aux[->[_,_], ⊙[_,_], I[_]] = Ccc.Aux[ArrowK[->, *, *], ⊙, ->, IsKind, TypeK[I]]

type InitialK[->[_,_]] = Initial[ArrowK[->, *, *]] { type TC[a] = IsKind[a] }
object InitialK:
  type Aux[->[_,_], I[_]] = Initial.Aux[ArrowK[->, *, *], IsKind, TypeK[I]]

type TerminalK[->[_,_]] = Terminal[ArrowK[->, *, *]] { type TC[a] = IsKind[a] }
object TerminalK:
  type Aux[->[_,_], I[_]] = Terminal.Aux[ArrowK[->, *, *], IsKind, TypeK[I]]

