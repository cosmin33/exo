package io.cosmo.exo.categories

import io.cosmo.exo._

trait Groupoid[->[_,_]] extends Subcat[->]:
  def flip[A, B](f: A -> B): B -> A
object Groupoid:
  type Aux[->[_,_], C[_]] = Groupoid[->] { type TC[a] = C[a] }
  type AuxT[->[_,_]] = Aux[->, Trivial]
  def apply[->[_,_]](using g: Groupoid[->]): Groupoid[->] = g

trait GroupoidK[->[_,_]] extends SubcategoryK[->]:
  def flip[F[_], G[_]](f: ∀[[a] =>> F[a] -> G[a]]): ∀[[a] =>> G[a] -> F[a]]
object GroupoidK:
  type Aux[->[_,_], C[_[_]]] = GroupoidK[->] { type TC[a[_]] = C[a] }
  type AuxT[->[_,_]] = Aux[->, TrivialK]
  def apply[->[_,_]](using g: GroupoidK[->]): GroupoidK[->] = g

trait GroupoidK2[->[_,_]] extends SubcategoryK2[->]:
  def flip[F[_,_], G[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]]): ∀∀[[a, b] =>> G[a, b] -> F[a, b]]
object GroupoidK2:
  type Aux[->[_,_], C[_[_,_]]] = GroupoidK2[->] { type TC[a[_,_]] = C[a] }
  type AuxT[->[_,_]] = Aux[->, TrivialK2]
  def apply[->[_,_]](using g: GroupoidK2[->]): GroupoidK2[->] = g

trait GroupoidH[->[_,_]] extends SubcategoryH[->]:
  def flip[F[_[_]], G[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]]): ∀~[[a[_]] =>> G[a] -> F[a]]
object GroupoidH:
  type Aux[->[_,_], C[_[_[_]]]] = GroupoidH[->] { type TC[a[_[_]]] = C[a] }
  type AuxT[->[_,_]] = Aux[->, TrivialH]
  def apply[->[_,_]](using g: GroupoidH[->]): GroupoidH[->] = g
