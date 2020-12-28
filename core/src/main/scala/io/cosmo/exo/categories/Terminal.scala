package io.cosmo.exo.categories

import io.cosmo.exo.{<=>, Iso}

trait Terminal[->[_, _]] extends Subcat[->] {
  type Terminal
  def terminalTC : TC[Terminal]

  def terminate[A](implicit A: TC[A]): A -> Terminal
}

object Terminal {
  type AuxTerm[->[_,_], T] = Terminal[->] { type Terminal = T }
  type Aux[->[_,_], C[_], T] = Terminal[->] { type TC[a] = C[a]; type Terminal = T }
  trait Proto[->[_, _], ->#[_], T] extends Terminal[->] with Subcat.Proto[->, ->#] {
    type Terminal = T
  }

  implicit def isoUnit[->[_,_], TC[_], Term, A](implicit
    t: Terminal.Aux[->, TC, Term],
    tc: TC[A]
  ): (A -> Term) <=> Unit = Iso.unsafe((_: A -> Term) => (), (_: Unit) => t.terminate[A])
}
