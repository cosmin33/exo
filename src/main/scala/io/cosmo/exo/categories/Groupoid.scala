package io.cosmo.exo.categories

import io.cosmo.exo._

trait Groupoid[->[_, _]] extends Subcat[->] {
  def flip[A, B](f: A -> B): B -> A
}
object Groupoid {
  type Aux[->[_, _], C[_]] = Groupoid[->] { type TC[a] = C[a] }
  type AuxT[->[_, _]] = Aux[->, Trivial]
  def apply[->[_,_]](using g: Groupoid[->]): Groupoid[->] = g

}
