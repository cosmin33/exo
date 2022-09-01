package io.cosmo.exo.categories

trait Groupoid[->[_, _]] extends Subcat[->] {
  def flip[A, B](f: A -> B): B -> A
}
object Groupoid {
  type Aux[->[_, _], C[_]] = Groupoid[->] { type TC[a] = C[a] }
  type AuxT[->[_, _]] = Aux[->, Trivial.T1]
  def apply[->[_,_]](implicit g: Groupoid[->]): Groupoid[->] = g

  trait Proto[->[_, _], TC[_]] extends Groupoid[->] with Subcat.Proto[->, TC]

}
