package io.cosmo.exo.categories

import io.cosmo.exo._
import shapeless.the

trait Groupoid[->[_, _]] extends Subcat[->] {
  def flip[A, B](f: A -> B): B -> A
}
object Groupoid {
  type Aux[->[_, _], C[_]] = Groupoid[->] { type TC[a] = C[a] }
  type AuxT[->[_, _]] = Aux[->, Trivial.T1]
  def apply[->[_,_]: Groupoid]: Groupoid[->] = the[Groupoid[->]]

  trait Proto[->[_, _], TC[_]] extends Groupoid[->] with Subcat.Proto[->, TC]

  def isoIso[->[_,_], A, B](implicit G: Groupoid[->]): (A -> B) <=> Iso[->, A, B] =
    Iso.unsafe(eq => Iso.unsafe(eq, G.flip(eq)), ieq => ieq.to)

  def isoFlip[->[_,_]: Groupoid, A, B]: (A -> B) <=> (B -> A) = Iso.unsafe(Groupoid[->].flip, Groupoid[->].flip)
}

//trait GroupoidK[->[_[_], _[_]]] extends CategoryK[->] {
//  def flip[A[_], B[_]](f: A -> B): B -> A
//}
//object GroupoidK {
//  trait Aux[->[_[_], _[_]], TC[_[_]]] extends GroupoidK[->] with CategoryK.Aux[->, TC]
//  trait AuxT[->[_[_], _[_]]] extends Aux[->, Trivial.T2]
//}
