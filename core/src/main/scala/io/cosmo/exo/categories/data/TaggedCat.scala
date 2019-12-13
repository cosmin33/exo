package io.cosmo.exo.categories.data

import cats.data.Tuple2K
import io.cosmo.exo.categories.{Subcat, Semicategory}

final case class TaggedCat[->[_,_], T[_], A, B](run: A -> B, ev: EvidenceCat[T, A, B]) { ab =>
  def andThen[C](bc: TaggedCat[->, T, B, C])(implicit C: Semicategory[->]): TaggedCat[->, T, A, C] =
    TaggedCat(C.andThen(ab.run, bc.run), ab.ev andThen bc.ev)
}
object Tagged {

  def taggedFunctionCategory[T[_]]: Subcat.Aux[TaggedCat[Function1, T, *, *], T] =
    new Subcat[TaggedCat[Function1, T, *, *]] {
      type TC[a] = T[a]
      def id[A](implicit tc: T[A]) = TaggedCat(identity[A], EvidenceCat.id[T, A](tc))
      override def andThen[A, B, C](ab: TaggedCat[* => *, T, A, B], bc: TaggedCat[* => *, T, B, C])
      : TaggedCat[* => *, T, A, C] = TaggedCat(bc.run compose ab.run, bc.ev compose ab.ev)
    }

  def category[T[_], ->[_, _], T0[_]](C: Subcat.Aux[->, T0]): Subcat.Aux[TaggedCat[->, T, *, *], Tuple2K[T, T0, *]] =
    new Subcat[TaggedCat[->, T, *, *]] {
      type TC[a] = Tuple2K[T, T0, a]
      def id[A](implicit A: TC[A]) = TaggedCat(C.id[A](A.second), EvidenceCat.id(A.first))
      def andThen[A, B, C](ab: TaggedCat[->, T, A, B], bc: TaggedCat[->, T, B, C]): TaggedCat[->, T, A, C] =
        TaggedCat(C.andThen[A, B, C](ab.run, bc.run), bc.ev compose ab.ev)
    }
}
