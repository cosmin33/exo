package io.cosmo.exo.categories.data

import cats.data.Tuple2K
import io.cosmo.exo.categories.{Dual, Semicategory, Subcat}

final case class ProdCat[==>[_,_], -->[_,_], A, B](first: A ==> B, second: A --> B) { ab =>
  def andThen[C](bc: ProdCat[==>, -->, B, C])(implicit C: Semicategory[==>], D: Semicategory[-->]): ProdCat[==>, -->, A, C] =
    ProdCat(C.andThen(ab.first, bc.first), D.andThen(ab.second, bc.second))
}

object ProdCat {
  type BicatEndo[->[_,_], A, B] = ProdCat[->,     ->   , A, B]
  type Dicat[->[_,_], A, B] = ProdCat[->, Dual[->,*,*], A, B]
  object Dicat {
    def apply[->[_,_], A, B](to: A -> B, from: B -> A): Dicat[->, A, B] = new Dicat(to, Dual(from))
  }

  def id[==>[_,_], =>#[_], -->[_,_], ->#[_], A](implicit
    C: Subcat.Aux[==>, =>#],
    AC: =>#[A],
    D: Subcat.Aux[-->, ->#],
    AD: ->#[A],
  ): ProdCat[==>, -->, A, A] = ProdCat(C.id[A](AC), D.id[A](AD))

  def categoryTupledTc[==>[_,_], =>#[_], -->[_,_], ->#[_]](implicit
    C: Subcat.Aux[==>, =>#], D: Subcat.Aux[-->, ->#]
  ): Subcat.Aux[ProdCat[==>, -->, *, *], Tuple2K[=>#, ->#, *]] =
    new Subcat[ProdCat[==>, -->, *, *]] {
      type TC[ᵒ] = Tuple2K[=>#, ->#, ᵒ]
      def id[A](implicit A: Tuple2K[=>#, ->#, A]): ProdCat[==>, -->, A, A] =
        ProdCat.id[==>, =>#, -->, ->#, A](C, A.first, D, A.second)
      def andThen[X, Y, Z](ab: ProdCat[==>, -->, X, Y], bc: ProdCat[==>, -->, Y, Z]): ProdCat[==>, -->, X, Z] =
        ab.andThen(bc)
    }

  implicit def categorySameTC[==>[_,_], -->[_,_], TC0[_]](implicit
    C: Subcat.Aux[==>, TC0],
    D: Subcat.Aux[-->, TC0]
  ): Subcat.Aux[ProdCat[==>, -->, *, *], TC0] =
      new Subcat[ProdCat[==>, -->, *, *]] {
        type TC[a] = TC0[a]
        def id[A](implicit A: TC[A]) = ProdCat.id[==>, TC, -->, TC, A](C, A, D, A)
        def andThen[A, B, C](ab: ProdCat[==>, -->, A, B], bc: ProdCat[==>, -->, B, C]) =
          ab.andThen(bc)
      }

}
