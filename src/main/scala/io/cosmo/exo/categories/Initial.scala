package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.internal._

trait Initial[->[_,_]]:
  type I
  type TC[_]
  def subcat: Subcat.Aux[->, TC]
  def TC : TC[I]
  def initiate[A](using A: TC[A]): I -> A

object Initial extends Function1InitialTerminalInstances
  with ProdcatInitialTerminalInstances:
  type Aux[->[_,_], C[_], Init] = Initial[->] {type TC[a] = C[a]; type I = Init}
  trait Proto[->[_,_], C[_], Init] extends Initial[->] { type TC[a] = C[a]; type I = Init }

  given isoUnit[->[_,_], TC[_], Init, A](using i: Initial.Aux[->, TC, Init], tc: TC[A]): ((Init -> A) <=> Unit) =
    Iso.unsafe((_: Init -> A) => (), (_: Unit) => i.initiate[A])
  
  extension [->[_,_], TC[_], Init](self: Terminal.Aux[->, TC, Init])
    def terminate[A](using A: TC[A]): A -> Init = self.initiate[A]

end Initial

type Terminal[->[_,_]] = Initial[Dual[->,*,*]]
object Terminal:
  type Aux[->[_,_], C[_], I] = Initial.Aux[Dual[->,*,*], C, I]
  trait Proto[->[_,_], C[_], Term] extends Initial.Proto[Dual[->,*,*], C, Term]:
    protected def terminate[A](using A: TC[A]): A -> Term
    override def initiate[A](using A: TC[A]): Dual[->, Term, A] = Dual(terminate[A])

trait InitialK[->[_,_]]:
  type I[_]
  type TC[_[_]]
  def subcat: SubcatK.Aux[->, TC]
  def TC : TC[I]
  def initiate[A[_]](using A: TC[A]): ∀[[a] =>> I[a] -> A[a]]

object InitialK:
  type Aux[->[_,_], C[_[_]], Init[_]] = InitialK[->] {type TC[a[_]] = C[a]; type I[a] = Init[a]}
  trait Proto[->[_,_], C[_[_]], Init[_]] extends InitialK[->] { type TC[a[_]] = C[a]; type I[a] = Init[a] }

  given isoUnitK[->[_,_], TC[_[_]], Init[_], A[_]](using i: InitialK.Aux[->, TC, Init], tc: TC[A]): ((∀[[a] =>> Init[a] -> A[a]]) <=> Unit) =
    Iso.unsafe(_ => (), _ => i.initiate[A])

  extension [->[_,_], C[_[_]], I[_]](self: TerminalK.Aux[->, C, I])
    def terminate[A[_]](using A: C[A]): ∀[[a] =>> A[a] -> I[a]] = ∀[[a] =>> A[a] -> I[a]](self.initiate[A].apply)

end InitialK

type TerminalK[->[_,_]] = InitialK[Dual[->,*,*]]
object TerminalK:
  type Aux[->[_,_], C[_[_]], I[_]] = InitialK.Aux[Dual[->,*,*], C, I]
  trait Proto[->[_,_], C[_[_]], Term[_]] extends InitialK.Proto[Dual[->,*,*], C, Term]:
    protected def terminate[A[_]](using A: TC[A]): ∀[[a] =>> A[a] -> Term[a]]
    override def initiate[A[_]](using A: TC[A]): ∀[[a] =>> Dual[->, Term[a], A[a]]] =
      ∀[[a] =>> Dual[->, Term[a], A[a]]](Dual(terminate[A].apply))

trait InitialK2[->[_,_]]:
  type I[_,_]
  type TC[_[_,_]]
  def subcat: SubcatK2.Aux[->, TC]
  def TC: TC[I]
  def initiate[F[_,_]](using F: TC[F]): ∀∀[[a, b] =>> I[a, b] -> F[a, b]]

object InitialK2:
  type Aux[->[_,_], C[_[_,_]], Init[_,_]] = InitialK2[->] { type TC[a[_,_]] = C[a]; type I[a, b] = Init[a, b] }
  trait Proto[->[_,_], C[_[_,_]], Init[_,_]] extends InitialK2[->] { type TC[a[_,_]] = C[a]; type I[a, b] = Init[a, b] }

  given isoUnitK2[->[_,_], TC[_[_,_]], Init[_,_], F[_,_]](using i: InitialK2.Aux[->, TC, Init], tc: TC[F]): ((∀∀[[a, b] =>> Init[a, b] -> F[a, b]]) <=> Unit) =
    Iso.unsafe(_ => (), _ => i.initiate[F])

  extension [->[_,_], C[_[_,_]], I[_,_]](self: TerminalK2.Aux[->, C, I])
    def terminate[F[_,_]](using F: C[F]): ∀∀[[a, b] =>> F[a, b] -> I[a, b]] = ∀∀[[a, b] =>> F[a, b] -> I[a, b]](self.initiate[F].apply)

end InitialK2

type TerminalK2[->[_,_]] = InitialK2[Dual[->,*,*]]
object TerminalK2:
  type Aux[->[_,_], C[_[_,_]], I[_,_]] = InitialK2.Aux[Dual[->,*,*], C, I]
  trait Proto[->[_,_], C[_[_,_]], Term[_,_]] extends InitialK2.Proto[Dual[->,*,*], C, Term]:
    protected def terminate[F[_,_]](using F: C[F]): ∀∀[[a, b] =>> F[a, b] -> Term[a, b]]
    override def initiate[F[_,_]](using F: C[F]): ∀∀[[a, b] =>> Dual[->, Term[a, b], F[a, b]]] =
      ∀∀[[a, b] =>> Dual[->, Term[a, b], F[a, b]]](Dual(terminate[F].apply))

trait InitialH[->[_,_]]:
  type I[_[_]]
  type TC[_[_[_]]]
  def subcat: SubcatH.Aux[->, TC]
  def TC: TC[I]
  def initiate[F[_[_]]](using F: TC[F]): ∀~[[a[_]] =>> I[a] -> F[a]]

object InitialH:
  type Aux[->[_,_], C[_[_[_]]], Init[_[_]]] = InitialH[->] { type TC[a[_[_]]] = C[a]; type I[a[_]] = Init[a] }
  trait Proto[->[_,_], C[_[_[_]]], Init[_[_]]] extends InitialH[->] { type TC[a[_[_]]] = C[a]; type I[a[_]] = Init[a] }

  given isoUnitH[->[_,_], TC[_[_[_]]], Init[_[_]], F[_[_]]](using i: InitialH.Aux[->, TC, Init], tc: TC[F]): ((∀~[[a[_]] =>> Init[a] -> F[a]]) <=> Unit) =
    Iso.unsafe(_ => (), _ => i.initiate[F])

  extension [->[_,_], C[_[_[_]]], I[_[_]]](self: TerminalH.Aux[->, C, I])
    def terminate[F[_[_]]](using F: C[F]): ∀~[[a[_]] =>> F[a] -> I[a]] = ∀~[[a[_]] =>> F[a] -> I[a]](self.initiate[F].apply)

end InitialH

type TerminalH[->[_,_]] = InitialH[Dual[->, *, *]]
object TerminalH:
  type Aux[->[_,_], C[_[_[_]]], I[_[_]]] = InitialH.Aux[Dual[->, *, *], C, I]
  trait Proto[->[_,_], C[_[_[_]]], Term[_[_]]] extends InitialH.Proto[Dual[->, *, *], C, Term]:
    protected def terminate[F[_[_]]](using F: TC[F]): ∀~[[a[_]] =>> F[a] -> Term[a]]
    override def initiate[F[_[_]]](using F: TC[F]): ∀~[[a[_]] =>> Dual[->, Term[a], F[a]]] =
      ∀~[[a[_]] =>> Dual[->, Term[a], F[a]]](Dual(terminate[F].apply))
