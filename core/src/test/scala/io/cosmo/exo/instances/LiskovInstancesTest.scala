package io.cosmo.exo.instances

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*

object LiskovInstancesTest {
  /////////////////// Subcategory Hierarchy ///////////////////
  summon[Subcat.Aux[<~<, Trivial]]
  summon[Subcat.Aux[Dual[<~<,*,*], Trivial]]
  summon[Subcat.Aux[>~>, Trivial]]
  summon[Distributive.Aux[<~<, Trivial, &, Any, |, Void]]

  /////////////////// Associative Hierarchy ///////////////////
  summon[Associative.Aux[<~<, &, Trivial]]
  summon[Braided.Aux[<~<, &, Trivial]]
  summon[Symmetric.Aux[<~<, &, Trivial]]
  summon[Monoidal.Aux[<~<, &, Trivial, Any]]
  summon[Cartesian.Aux[<~<, &, Trivial, Any]]

  summon[Associative.Aux[Dual[<~<,*,*], &, Trivial]]
  summon[Braided.Aux[Dual[<~<,*,*], &, Trivial]]
  summon[Symmetric.Aux[Dual[<~<,*,*], &, Trivial]]
  summon[Monoidal.Aux[Dual[<~<,*,*], &, Trivial, Any]]

  summon[Associative.Aux[>~>, &, Trivial]]
  summon[Braided.Aux[>~>, &, Trivial]]
  summon[Symmetric.Aux[>~>, &, Trivial]]
  summon[Monoidal.Aux[>~>, &, Trivial, Any]]

  summon[Associative.Aux[Dual[<~<,*,*], |, Trivial]]
  summon[Braided.Aux[Dual[<~<,*,*], |, Trivial]]
  summon[Symmetric.Aux[Dual[<~<,*,*], |, Trivial]]
  summon[Monoidal.Aux[Dual[<~<,*,*], |, Trivial, Void]]
  summon[Cocartesian.Aux[<~<, |, Trivial, Void]]

  summon[Associative.Aux[>~>, |, Trivial]]
  summon[Braided.Aux[>~>, |, Trivial]]
  summon[Symmetric.Aux[>~>, |, Trivial]]
  summon[Monoidal.Aux[>~>, |, Trivial, Void]]

  summon[Associative.Aux[<~<, |, Trivial]]
  summon[Braided.Aux[<~<, |, Trivial]]
  summon[Symmetric.Aux[<~<, |, Trivial]]
  summon[Monoidal.Aux[<~<, |, Trivial, Void]]

  /////////////////// Initial, Terminal ///////////////////
  summon[Initial[<~<]]
  summon[Terminal[<~<]]
}
