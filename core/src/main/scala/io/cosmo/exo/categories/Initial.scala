package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.internal._

type Terminal[->[_, _]] = Initial[Dual[->,*,*]]
object Terminal:
  type Aux[->[_,_], C[_], I] = Initial.Aux[Dual[->,*,*], C, I]
  trait Proto[->[_,_], C[_], I] extends Initial.Proto[Dual[->,*,*], C, I]:
    protected def terminate[A](using A: TC[A]): A -> I
    override def initiate[A](using A: TC[A]): Dual[->, I, A] = Dual(terminate[A])

trait Initial[->[_, _]]:
  type Initial
  type TC[_]
  def subcat: Subcat.Aux[->, TC]
  def TC : TC[Initial]
  def initiate[A](using A: TC[A]): Initial -> A

object Initial extends Function1InitialTerminalInstances:
  type Aux[->[_,_], C[_], I] = Initial[->] {type TC[a] = C[a]; type Initial = I}
  trait Proto[->[_, _], C[_], I] extends Initial[->] { type TC[a] = C[a]; type Initial = I }

  given isoUnit[->[_,_], TC[_], Init, A](using i: Initial.Aux[->, TC, Init], tc: TC[A]): ((Init -> A) <=> Unit) =
    Iso.unsafe((_: Init -> A) => (), (_: Unit) => i.initiate[A])
  
  extension [->[_,_], TC[_], Init](self: Terminal.Aux[->, TC, Init])
    def terminate[A](using A: TC[A]): A -> Init = self.initiate[A]
