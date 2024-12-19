  package io.cosmo.exo.categories

  import io.cosmo.exo.evidence.*
  import io.cosmo.exo.internal.any.*
  import io.cosmo.exo.*

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

  //////////////// Categories for kind F[_] ////////////////

  type SemicategoryK[->[_,_]] = Semicategory[ArrowK[->,*,*]]
  type SubcategoryK[->[_,_]] = Subcategory.Aux[ArrowK[->,*,*], IsKind]
  type DistributiveK[->[_,_], ⨂[_, _], ⨁[_, _]] = Distributive.Aux1[ArrowK[->,*,*], IsKind, ⨂, ⨁]
  object DistributiveK:
    type Aux[->[_,_], ⨂[_,_], ⨁[_,_], P[_], S[_]] = Distributive.Aux[ArrowK[->,*,*], IsKind, ⨂, TypeK[P], ⨁, TypeK[S]]

  type AssociativeK[->[_,_], ⊙[_,_]] = Associative.Aux[ArrowK[->,*,*], ⊙, IsKind]
  type CoAssociativeK[->[_,_], ⊙[_,_]] = Associative.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind]

  type BraidedK[->[_,_], ⊙[_,_]] = Braided.Aux[ArrowK[->,*,*], ⊙, IsKind]
  type CoBraidedK[->[_,_], ⊙[_,_]] = Braided.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind]

  type SymmetricK[->[_,_], ⊙[_,_]] = Symmetric.Aux[ArrowK[->,*,*], ⊙, IsKind]
  type CoSymmetricK[->[_,_], ⊙[_,_]] = Symmetric.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind]

  type MonoidalK[->[_,_], ⊙[_,_]] = Monoidal[ArrowK[->,*,*], ⊙] { type TC[a] = IsKind[a] }
  object MonoidalK:
    type Aux[->[_,_], ⊙[_,_], I[_]] = Monoidal.Aux[ArrowK[->,*,*], ⊙, IsKind, TypeK[I]]
  type CoMonoidalK[->[_,_], ⊙[_,_]] = Monoidal[Dual[ArrowK[->,*,*],*,*], ⊙] { type TC[a] = IsKind[a] }
  object CoMonoidalK:
    type Aux[->[_,_], ⊙[_,_], I[_]] = Monoidal.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind, TypeK[I]]

  type CartesianK[->[_,_], ⊙[_,_]] = Cartesian[ArrowK[->,*,*], ⊙] { type TC[a] = IsKind[a] }
  object CartesianK:
    type Aux[->[_,_], ⊙[_,_], I[_]] = Cartesian.Aux[ArrowK[->,*,*], ⊙, IsKind, TypeK[I]]
  type CocartesianK[->[_,_], ⊙[_,_]] = Cartesian[Dual[ArrowK[->,*,*],*,*], ⊙] { type TC[a] = IsKind[a] }
  object CocartesianK:
    type Aux[->[_,_], ⊙[_,_], I[_]] = Cartesian.Aux[Dual[ArrowK[->,*,*],*,*], ⊙, IsKind, TypeK[I]]

  type CccK[->[_,_], ⊙[_,_]] = Ccc[ArrowK[->,*,*], ⊙, ->] { type TC[a] = IsKind[a] }
  object CccK:
    type Aux[->[_,_], ⊙[_,_], I[_]] = Ccc.Aux[ArrowK[->,*,*], ⊙, ->, IsKind, TypeK[I]]

  type InitialK[->[_,_]] = Initial[ArrowK[->,*,*]] { type TC[a] = IsKind[a] }
  object InitialK:
    type Aux[->[_,_], I[_]] = Initial.Aux[ArrowK[->,*,*], IsKind, TypeK[I]]

  type TerminalK[->[_,_]] = Terminal[ArrowK[->,*,*]] { type TC[a] = IsKind[a] }
  object TerminalK:
    type Aux[->[_,_], I[_]] = Terminal.Aux[ArrowK[->,*,*], IsKind, TypeK[I]]

  //////////////// Categories for kind F[_,_] ////////////////

  type AssociativeK2[->[_,_], ⊙[_,_]] = Associative.Aux[ArrowK2[->,*,*], ⊙, IsKind2]
  type CoAssociativeK2[->[_,_], ⊙[_,_]] = Associative.Aux[Dual[ArrowK2[->,*,*], *, *], ⊙, IsKind2]

  type BraidedK2[->[_,_], ⊙[_,_]] = Braided.Aux[ArrowK2[->,*,*], ⊙, IsKind2]
  type CoBraidedK2[->[_,_], ⊙[_,_]] = Braided.Aux[Dual[ArrowK2[->,*,*], *, *], ⊙, IsKind2]

  type SymmetricK2[->[_,_], ⊙[_,_]] = Symmetric.Aux[ArrowK2[->,*,*], ⊙, IsKind2]
  type CoSymmetricK2[->[_,_], ⊙[_,_]] = Symmetric.Aux[Dual[ArrowK2[->,*,*], *, *], ⊙, IsKind2]

  type MonoidalK2[->[_,_], ⊙[_,_]] = Monoidal[ArrowK2[->,*,*], ⊙] { type TC[a] = IsKind2[a] }
  object MonoidalK2:
    type Aux[->[_,_], ⊙[_,_], I[_,_]] = Monoidal.Aux[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[I]]
  type CoMonoidalK2[->[_,_], ⊙[_,_]] = Monoidal[Dual[ArrowK2[->,*,*], *, *], ⊙] { type TC[a] = IsKind2[a] }
  object CoMonoidalK2:
    type Aux[->[_,_], ⊙[_,_], I[_,_]] = Monoidal.Aux[Dual[ArrowK2[->,*,*], *, *], ⊙, IsKind2, TypeK2[I]]

  type CartesianK2[->[_,_], ⊙[_,_]] = Cartesian[ArrowK2[->,*,*], ⊙] { type TC[a] = IsKind2[a] }
  object CartesianK2:
    type Aux[->[_,_], ⊙[_,_], I[_,_]] = Cartesian.Aux[ArrowK2[->,*,*], ⊙, IsKind2, TypeK2[I]]
  type CocartesianK2[->[_,_], ⊙[_,_]] = Cartesian[Dual[ArrowK2[->,*,*], *, *], ⊙] { type TC[a] = IsKind2[a] }
  object CocartesianK2:
    type Aux[->[_,_], ⊙[_,_], I[_,_]] = Cartesian.Aux[Dual[ArrowK2[->,*,*], *, *], ⊙, IsKind2, TypeK2[I]]

  type CccK2[->[_,_], ⊙[_,_]] = Ccc[ArrowK2[->,*,*], ⊙, ->] { type TC[a] = IsKind2[a] }
  object CccK2:
    type Aux[->[_,_], ⊙[_,_], I[_,_]] = Ccc.Aux[ArrowK2[->,*,*], ⊙, ->, IsKind2, TypeK2[I]]

  type InitialK2[->[_,_]] = Initial[ArrowK2[->,*,*]] { type TC[a] = IsKind2[a] }
  object InitialK2:
    type Aux[->[_,_], I[_,_]] = Initial.Aux[ArrowK2[->,*,*], IsKind2, TypeK2[I]]

  type TerminalK2[->[_,_]] = Terminal[ArrowK2[->,*,*]] { type TC[a] = IsKind2[a] }
  object TerminalK2:
    type Aux[->[_,_], I[_,_]] = Terminal.Aux[ArrowK2[->,*,*], IsKind2, TypeK2[I]]

  //////////////// Categories for kinds F[_[_]] ////////////////

  type AssociativeHK[->[_,_], ⊙[_,_]] = Associative.Aux[ArrowH[->,*,*], ⊙, IsHKind]
  type CoAssociativeHK[->[_,_], ⊙[_,_]] = Associative.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind]

  type BraidedHK[->[_,_], ⊙[_,_]] = Braided.Aux[ArrowH[->,*,*], ⊙, IsHKind]
  type CoBraidedHK[->[_,_], ⊙[_,_]] = Braided.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind]

  type SymmetricHK[->[_,_], ⊙[_,_]] = Symmetric.Aux[ArrowH[->,*,*], ⊙, IsHKind]
  type CoSymmetricHK[->[_,_], ⊙[_,_]] = Symmetric.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind]

  type MonoidalHK[->[_,_], ⊙[_,_]] = Monoidal[ArrowH[->,*,*], ⊙] { type TC[a] = IsHKind[a] }
  object MonoidalHK:
    type Aux[->[_,_], ⊙[_,_], I[_[_]]] = Monoidal.Aux[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[I]]

  type CoMonoidalHK[->[_,_], ⊙[_,_]] = Monoidal[Dual[ArrowH[->,*,*],*,*], ⊙] { type TC[a] = IsHKind[a] }
  object CoMonoidalHK:
    type Aux[->[_,_], ⊙[_,_], I[_[_]]] = Monoidal.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind, TypeHK[I]]

  type CartesianHK[->[_,_], ⊙[_,_]] = Cartesian[ArrowH[->,*,*], ⊙] { type TC[a] = IsHKind[a] }
  object CartesianHK:
    type Aux[->[_,_], ⊙[_,_], I[_[_]]] = Cartesian.Aux[ArrowH[->,*,*], ⊙, IsHKind, TypeHK[I]]

  type CocartesianHK[->[_,_], ⊙[_,_]] = Cartesian[Dual[ArrowH[->,*,*],*,*], ⊙] { type TC[a] = IsHKind[a] }
  object CocartesianHK:
    type Aux[->[_,_], ⊙[_,_], I[_[_]]] = Cartesian.Aux[Dual[ArrowH[->,*,*],*,*], ⊙, IsHKind, TypeHK[I]]

  type CccHK[->[_,_], ⊙[_,_]] = Ccc[ArrowH[->,*,*], ⊙, ->] { type TC[a] = IsHKind[a] }
  object CccHK:
    type Aux[->[_,_], ⊙[_,_], I[_[_]]] = Ccc.Aux[ArrowH[->,*,*], ⊙, ->, IsHKind, TypeHK[I]]

  type InitialHK[->[_,_]] = Initial[ArrowH[->,*,*]] { type TC[a] = IsHKind[a] }
  object InitialHK:
    type Aux[->[_,_], I[_[_]]] = Initial.Aux[ArrowH[->,*,*], IsHKind, TypeHK[I]]

  type TerminalHK[->[_,_]] = Terminal[ArrowH[->,*,*]] { type TC[a] = IsHKind[a] }
  object TerminalHK:
    type Aux[->[_,_], I[_[_]]] = Terminal.Aux[ArrowH[->,*,*], IsHKind, TypeHK[I]]

