package io.cosmo.exo.categories

type Prodcat[==>[_,_], -->[_,_], A, B] = (A ==> B, A --> B)

type Opp[->[_,_]] = {type l[A, B] = B -> A}

type Dicat[->[_,_], A, B] = (A -> B, Dual[->, A, B])
object Dicat {
  def apply[->[_,_], A, B](to: A -> B, from: B -> A): Dicat[->, A, B] = (to, Dual(from))
}
