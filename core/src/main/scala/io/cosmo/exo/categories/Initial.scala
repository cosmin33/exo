package io.cosmo.exo.categories

import io.cosmo.exo.{<=>, Iso}

trait Initial[->[_, _]] extends Subcat[->] {
  type Initial
  def initialTC : TC[Initial]

  def initiate[A](implicit A: TC[A]): Initial -> A
}

object Initial {
  type Aux[->[_,_], C[_], I] = Initial[->] {type TC[a] = C[a]; type Initial = I}
  trait Proto[->[_, _], C0[_], I] extends Initial[->] with Subcat.Proto[->, C0] {
    type Initial = I
  }

  implicit def isoUnit[->[_,_], TC[_], Init, A](implicit
    i: Initial.Aux[->, TC, Init],
    tc: TC[A]
  ): (Init -> A) <=> Unit =
    Iso.unsafe((_: Init -> A) => (), (_: Unit) => i.initiate[A])
}
