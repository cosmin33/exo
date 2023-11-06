package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.internal._

type Terminal[->[_,_]] = Initial[Dual[->,*,*]]
object Terminal:
  type Aux[->[_,_], C[_], I] = Initial.Aux[Dual[->,*,*], C, I]
  trait Proto[->[_,_], C[_], Term] extends Initial.Proto[Dual[->,*,*], C, Term]:
    protected def terminate[A](using A: TC[A]): A -> Term
    override def initiate[A](using A: TC[A]): Dual[->, Term, A] = Dual(terminate[A])

trait Initial[->[_, _]]:
  type I
  type TC[_]
  def subcat: Subcat.Aux[->, TC]
  def TC : TC[I]
  def initiate[A](using A: TC[A]): I -> A

object Initial extends Function1InitialTerminalInstances
  with ProdcatInitialTerminalInstances:
  type Aux[->[_,_], C[_], Init] = Initial[->] {type TC[a] = C[a]; type I = Init}
  trait Proto[->[_, _], C[_], Init] extends Initial[->] { type TC[a] = C[a]; type I = Init }

  given isoUnit[->[_,_], TC[_], Init, A](using i: Initial.Aux[->, TC, Init], tc: TC[A]): ((Init -> A) <=> Unit) =
    Iso.unsafe((_: Init -> A) => (), (_: Unit) => i.initiate[A])
  
  extension [->[_,_], TC[_], Init](self: Terminal.Aux[->, TC, Init])
    def terminate[A](using A: TC[A]): A -> Init = self.initiate[A]
