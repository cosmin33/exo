package io.cosmo.exo.categories

import io.cosmo.exo._

trait Concrete[->[_, _]] extends Subcat[->]:
  def concretize[A, B](f: A -> B): (A, TC[A]) => (B, TC[B])
  def toFunction[A: TC, B](f: A -> B): A => B = concretize(f)(_, summon)._1

object Concrete:
  type Aux[->[_, _], C0[_]] = Concrete[->] { type TC[ᵒ] = C0[ᵒ] }
  type AuxT[->[_, _]] = Aux[->, Trivial]
