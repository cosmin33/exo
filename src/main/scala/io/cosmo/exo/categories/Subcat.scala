package io.cosmo.exo.categories

import io.cosmo.exo.*

type Subcat[->[_,_]] = Subcategory[->]
val Subcat: Subcategory.type = Subcategory
type SubcatK[->[_,_]] = SubcategoryK[->]
val SubcatK: SubcategoryK.type = SubcategoryK
type SubcatK2[->[_,_]] = SubcategoryK2[->]
val SubcatK2: SubcategoryK2.type = SubcategoryK2
type SubcatH[->[_,_]] = SubcategoryH[->]
val SubcatH: SubcategoryH.type = SubcategoryH

trait Subcategory[->[_,_]] extends Semicategory[->]:
  type TC[_]
  def id[A: TC]: A -> A
object Subcategory:
  type Aux[->[_,_], TC0[_]] = Subcat[->] { type TC[A] = TC0[A] }
  type AuxT[->[_,_]] = Subcat[->] { type TC[A] = Trivial[A] }
  def apply[->[_,_]](using S: Subcat[->]): Subcat[->] = S
  trait Proto[->[_,_], ->#[_]] extends Subcat[->] {type TC[a] = ->#[a]}

trait SubcatHasId[->[_,_], A]:
  type TC[_]
  val s: Subcat.Aux[->, TC]
  val id: A -> A
object SubcatHasId:
  def apply[->[_,_], A](using sub: SubcatHasId[->, A]): SubcatHasId[->, A] = sub
  given from[->[_,_], A, T[_]](using sub: Subcat.Aux[->, T], tc: T[A]): SubcatHasId[->, A] =
    new SubcatHasId[->, A] { type TC[a] = T[a]; val s = sub; val id = sub.id }

trait SubcategoryK[->[_,_]] extends SemicategoryK[->]:
  type TC[_[_]]
  def id[F[_]: TC]: ∀[[a] =>> F[a] -> F[a]]
object SubcategoryK:
  type Aux[->[_,_], TC0[_[_]]] = SubcategoryK[->] { type TC[a[_]] = TC0[a] }
  type AuxT[->[_,_]] = SubcategoryK[->] { type TC[a[_]] = TrivialK[a] }
  def apply[->[_,_]](using ev: SubcategoryK[->]): SubcategoryK[->] = ev
  trait Proto[->[_,_], TC0[_[_]]] extends SubcategoryK[->] { type TC[a[_]] = TC0[a] }

trait SubcatKHasId[->[_,_], F[_]]:
  type TC[_[_]]
  val s: SubcategoryK.Aux[->, TC]
  def id: ∀[[a] =>> F[a] -> F[a]]
object SubcatKHasId:
  def apply[->[_,_], F[_]](using sub: SubcatKHasId[->, F]): SubcatKHasId[->, F] = sub
  given from[->[_,_], F[_], T[_[_]]](using sub: SubcategoryK.Aux[->, T], tc: T[F]): SubcatKHasId[->, F] =
    new SubcatKHasId[->, F] { type TC[a[_]] = T[a]; val s = sub; def id = sub.id }

trait SubcategoryK2[->[_,_]] extends SemicategoryK2[->]:
  type TC[_[_,_]]
  def id[F[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] -> F[a, b]]
object SubcategoryK2:
  type Aux[->[_,_], TC0[_[_,_]]] = SubcategoryK2[->] { type TC[a[_,_]] = TC0[a] }
  type AuxT[->[_,_]] = SubcategoryK2[->] { type TC[a[_,_]] = TrivialK2[a] }
  def apply[->[_,_]](using ev: SubcategoryK2[->]): SubcategoryK2[->] = ev
  trait Proto[->[_,_], TC0[_[_,_]]] extends SubcategoryK2[->] { type TC[a[_,_]] = TC0[a] }

trait SubcatK2HasId[->[_,_], F[_,_]]:
  type TC[_[_,_]]
  val s: SubcategoryK2.Aux[->, TC]
  def id: ∀∀[[a, b] =>> F[a, b] -> F[a, b]]
object SubcatK2HasId:
  def apply[->[_,_], F[_,_]](using sub: SubcatK2HasId[->, F]): SubcatK2HasId[->, F] = sub
  given from[->[_,_], F[_,_], T[_[_,_]]](using sub: SubcategoryK2.Aux[->, T], tc: T[F]): SubcatK2HasId[->, F] =
    new SubcatK2HasId[->, F] { type TC[a[_,_]] = T[a]; val s = sub; def id = sub.id }

trait SubcategoryH[->[_,_]] extends SemicategoryH[->]:
  type TC[_[_[_]]]
  def id[F[_[_]]: TC]: ∀~[[a[_]] =>> F[a] -> F[a]]
object SubcategoryH:
  type Aux[->[_,_], TC0[_[_[_]]]] = SubcategoryH[->] { type TC[a[_[_]]] = TC0[a] }
  type AuxT[->[_,_]] = SubcategoryH[->] { type TC[a[_[_]]] = TrivialH[a] }
  def apply[->[_,_]](using ev: SubcategoryH[->]): SubcategoryH[->] = ev
  trait Proto[->[_,_], TC0[_[_[_]]]] extends SubcategoryH[->] { type TC[a[_[_]]] = TC0[a] }

trait SubcatHHasId[->[_,_], F[_[_]]]:
  type TC[_[_[_]]]
  val s: SubcategoryH.Aux[->, TC]
  def id: ∀~[[a[_]] =>> F[a] -> F[a]]
object SubcatHHasId:
  def apply[->[_,_], F[_[_]]](using sub: SubcatHHasId[->, F]): SubcatHHasId[->, F] = sub
  given from[->[_,_], F[_[_]], T[_[_[_]]]](using sub: SubcategoryH.Aux[->, T], tc: T[F]): SubcatHHasId[->, F] =
    new SubcatHHasId[->, F] { type TC[a[_[_]]] = T[a]; val s = sub; def id = sub.id }

