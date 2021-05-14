package io.cosmo.exo.categories.data

import cats.implicits._
import io.cosmo.exo.categories.functors.{Exobifunctor, LaxSemigroupal, OplaxSemigroupal}
import io.cosmo.exo.categories.syntax._
import io.cosmo.exo.categories.{Semicategory, Subcat, Trivial}
import io.cosmo.exo._

final case class DeductionCat[->[_,_], F[_], G[_], A, B](fn: F[A] -> G[B])

object DeductionCat {
import DeductionCatHelpers._

  implicit def bifunctorProd[==>[_,_], -->[_,_], ~~>[_,_], ⊙[_,_], T[_], F[_], G[_]](implicit
    S: Semicategory[~~>],
    LS: LaxSemigroupal[⊙, ~~>, ⊙, G],
    OS: OplaxSemigroupal[⊙, ~~>, ⊙, F],
    F: Exobifunctor[==>, -->, ~~>, ⊙]
  ): Exobifunctor[DeductionCat[==>, F, G,*,*], DeductionCat[-->, F, G,*,*], DeductionCat[~~>, F, G,*,*], ⊙] =
    new Exobifunctor[DeductionCat[==>, F, G,*,*], DeductionCat[-->, F, G,*,*], DeductionCat[~~>, F, G,*,*], ⊙] {
      def bimap[A, X, B, Y](left: DeductionCat[==>, F, G, A, X], right: DeductionCat[-->, F, G, B, Y]): DeductionCat[~~>, F, G, A ⊙ B, X ⊙ Y] =
        DeductionCat(OS.opProduct[A, B] >>>> F.bimap(left.fn, right.fn) >>>> LS.product[X, Y])
    }

  trait SubcatDeductionCat[->[_,_], T[_], F[_], G[_]] extends Subcat[DeductionCat[->, F, G, *, *]] {
    protected def sub: Subcat.Aux[->, T]
    protected def ft: T ~> λ[a => T[F[a]]]
    protected def fg: ∀[λ[a => T[a] => (F[a] -> G[a])]]
    type TC[a] = T[a]
    def id[A](implicit ta: T[A]): DeductionCat[->, F, G, A, A] = DeductionCat(fg.apply[A](ta))
    def andThen[A, B, C](ab: DeductionCat[->, F, G, A, B], bc: DeductionCat[->, F, G, B, C]): DeductionCat[->, F, G, A, C] = {
      val a1: F[A] -> G[B] = ab.fn
      val a2: F[B] -> G[C] = bc.fn
      ??? //DeductionCat(sub.andThen(ab.fn, bc.fn))
    }
  }

}

object DeductionCatHelpers {

}