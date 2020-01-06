package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.evidence.=~=
import shapeless.the

trait Concrete[->[_, _]] extends Subcat[->] {
  def concretize[A, B](f: A -> B): (A, TC[A]) => (B, TC[B])

  def toFunction[A, B](f: A -> B)(implicit eq: Trivial.T1 =~= TC): A => B =
    concretize(f)(_, eq(the[Trivial.T1[A]]))._1

  def concretize1[A, B](a: A)(f: A -> B)(implicit A: TC[A]): B =
    concretize[A, B](f)(a, A)._1
}
object Concrete {
  type Aux[->[_, _], C0[_]] = Concrete[->] { type TC[ᵒ] = C0[ᵒ] }
  type AuxT[->[_, _]] = Aux[->, Trivial.T1]
  trait Proto[->[_, _], C0[_]] extends Concrete[->] with Subcat.Proto[->, C0]

}