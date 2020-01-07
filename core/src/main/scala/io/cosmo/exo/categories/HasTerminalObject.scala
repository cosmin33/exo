package io.cosmo.exo.categories

import io.cosmo.exo.{<=>, Iso}

trait HasTerminalObject[->[_, _]] extends Subcat[->] {
  type Terminal
  def terminal : TC[Terminal]

  def terminate[A](implicit A: TC[A]): A -> Terminal
}

object HasTerminalObject {
  type AuxTerm[->[_,_], T] = HasTerminalObject[->] { type Terminal = T }
  type Aux[->[_,_], C[_], T] = HasTerminalObject[->] { type TC[a] = C[a]; type Terminal = T }
  trait Proto[->[_, _], ->#[_], T] extends HasTerminalObject[->] with Subcat.Proto[->, ->#] {
    type Terminal = T
  }

  implicit def isoUnit[->[_,_], TC[_], Term, A](implicit
    t: HasTerminalObject.Aux[->, TC, Term],
    tc: TC[A]
  ): (A -> Term) <=> Unit = Iso.unsafe((_: A -> Term) => (), (_: Unit) => t.terminate[A])
}
