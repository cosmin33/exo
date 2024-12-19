package io.cosmo.exo.categories

import io.cosmo.exo.*

type Subcat[->[_,_]] = Subcategory[->]
val Subcat: Subcategory.type = Subcategory

trait Subcategory[->[_,_]] extends Semicategory[->]:
  type TC[_]
  def id[A](using A: TC[A]): A -> A

object Subcategory:
  type Aux[->[_,_], TC0[_]] = Subcat[->] { type TC[A] = TC0[A] }
  type AuxT[->[_,_]] = Subcat[->] { type TC[A] = Trivial[A] }

  def apply[->[_,_]](using S: Subcat[->]): Subcat[->] = S

  trait Proto[->[_,_], ->#[_]] extends Subcat[->] {type TC[a] = ->#[a]}
end Subcategory

trait SubcatHasId[->[_,_], A]:
  type TC[_]
  val s: Subcat.Aux[->, TC]
  val id: A -> A

object SubcatHasId:
  def apply[->[_,_], A](using sub: SubcatHasId[->, A]): SubcatHasId[->, A] = sub

  given from[->[_,_], A, T[_]](using sub: Subcat.Aux[->, T], tc: T[A]): SubcatHasId[->, A] =
    new SubcatHasId[->, A] { type TC[a] = T[a]; val s = sub; val id = sub.id }
end SubcatHasId
