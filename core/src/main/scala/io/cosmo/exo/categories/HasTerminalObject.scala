package io.cosmo.exo.categories

import io.cosmo.exo.{<=>, Iso}

trait HasTerminalObject[->[_, _]] extends Subcat[->] {
  type Terminal
  def terminal : TC[Terminal]

  def terminate[A](implicit A: TC[A]): A -> Terminal
}
object HasTerminalObject extends HasTerminalObjectInstances {
  type Aux[->[_,_], C[_], T] = HasTerminalObject[->] { type TC[a] = C[a]; type Terminal = T }
  trait Proto[C1[_, _], C0[_], T] extends HasTerminalObject[C1] with Subcat.Proto[C1, C0] {
    type Terminal = T
  }

  implicit def isoUnit[->[_,_], TC[_], Term, A](implicit
    t: HasTerminalObject.Aux[->, TC, Term],
    tc: TC[A]
  ): <=>[A -> Term, Unit] =
    Iso.unsafe((_: A -> Term) => (), (_: Unit) => t.terminate[A])

}

trait HasTerminalObjectInstances {

  trait HasTerminalObjectFunction1 extends HasTerminalObject.Proto[Function1, Trivial.T1, Unit] {
    override def terminal: Trivial.T1[Terminal] = Trivial.trivialInstance
    override def terminate[A](implicit A: Trivial.T1[A]): A => Terminal = _ => ()
  }

}