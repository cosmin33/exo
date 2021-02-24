package io.cosmo.exo.categories

trait Concrete[->[_, _]] extends Subcat[->] {
  def concretize[A, B](f: A -> B): (A, TC[A]) => (B, TC[B])

  def toFunction[A: TC, B](f: A -> B): A => B = concretize(f)(_, implicitly)._1

  def concrete[A: TC, B](a: A)(f: A -> B): B = concretize(f)(a, implicitly)._1
}
object Concrete {
  type Aux[->[_, _], C0[_]] = Concrete[->] { type TC[ᵒ] = C0[ᵒ] }
  type AuxT[->[_, _]] = Aux[->, Trivial.T1]
  trait Proto[->[_, _], C0[_]] extends Concrete[->] with Subcat.Proto[->, C0]
}