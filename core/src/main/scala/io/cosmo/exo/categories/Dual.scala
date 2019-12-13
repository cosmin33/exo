package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.evidence.{===, =~~=, Is, IsK2}

sealed trait DualModule {
  type Dual[->[_,_], A, B] <: B -> A

  def leibniz[->[_, _], A, B]: Dual[->, A, B] === (B -> A)
  def leibniz2[->[_,_]]: Dual[->,*,*] =~~= Opp[->]#l
  def apply[->[_, _], A, B](f: B -> A): Dual[->, A, B] = leibniz.flip(f)
}

object DualModule extends DualInstances {
  implicit class DualOps[->[_,_], A, B](private val d: Dual[->, A, B]) extends AnyVal {
  }

  implicit def conversion[->[_,_], A, B](ab: B -> A): Dual[->, A, B] = Dual(ab)
}

private[categories] object DualImpl extends DualModule {
  type Dual[->[_,_], A, B] = B -> A
  override def leibniz[->[_, _], A, B] = Is.refl
  override def leibniz2[->[_,_]] = IsK2.refl
}

trait DualInstances {
  implicit def category[->[_, _], T[_]](implicit C: Subcat.Aux[->, T]): Subcat.Aux[Dual[->, *, *], T] =
    new Subcat[Dual[->, *, *]] {
      override type TC[a] = T[a]
      override def id[A](implicit A: TC[A]): Dual[->, A, A] = Dual(C.id[A](A))
      override def andThen[A, B, C](ab: Dual[->, A, B], bc: Dual[->, B, C]): Dual[->, A, C] =
        Dual(C.andThen(bc, ab))
    }
}
