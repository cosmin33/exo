package io.cosmo.exo.categories

import io.cosmo.exo.evidence.{===, =~~=, Is, IsK2}

sealed trait DualModule {
  type Dual[->[_,_], A, B] <: B -> A

  def leibniz[->[_,_]]: Opp[->]#l =~~= Dual[->,*,*]
  def is[->[_, _], A, B]: (B -> A) === Dual[->, A, B] = leibniz[->].is[A, B]
  def apply[->[_, _], A, B](f: B -> A): Dual[->, A, B] = is(f)
}

object DualModule extends DualInstances {
  implicit class DualOps[->[_,_], A, B](private val self: Dual[->, A, B]) extends AnyVal {
    //def toFn: B -> A = Dual.leibniz[->].flip(self)
  }

  implicit def conversion[->[_,_], A, B](ab: B -> A): Dual[->, A, B] = Dual(ab)
}

private[categories] object DualImpl extends DualModule {
  type Dual[->[_,_], A, B] = B -> A
  override def leibniz[->[_,_]] = IsK2.refl
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
