package io.cosmo.exo.categories

import cats.evidence.{===, Is}
import io.cosmo.exo.{categories, _}

trait Groupoid[->[_, _]] extends Subcat[->] {
  def flip[A, B](f: A -> B): B -> A
}
object Groupoid {
  type Aux[->[_, _], C[_]] = Groupoid[->] { type TC[a] = C[a] }
  type AuxT[->[_, _]] = Aux[->, Trivial.T1]
  trait Proto[->[_, _], TC[_]] extends Groupoid[->] with Subcat.Proto[->, TC]

}

//trait GroupoidK[->[_[_], _[_]]] extends CategoryK[->] {
//  def flip[A[_], B[_]](f: A -> B): B -> A
//}
//object GroupoidK {
//  trait Aux[->[_[_], _[_]], TC[_[_]]] extends GroupoidK[->] with CategoryK.Aux[->, TC]
//  trait AuxT[->[_[_], _[_]]] extends Aux[->, Trivial.T2]
//}
