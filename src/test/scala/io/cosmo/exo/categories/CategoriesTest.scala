package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.internal.any.*

class CategoriesTest {

  summon[Semicategory[* => *]]
  summon[SemicategoryK[* => *]]
  summon[Groupoid[Iso[* => *, *, *]]]
  summon[GroupoidK[Iso[* => *, *, *]]]
  summon[Subcategory[* => *]]
  summon[SubcategoryK[* => *]]
  summon[Distributive[* => *, Tuple2, Either]]
  summon[Distributive[* => *, /\, \/]]
  summon[DistributiveK[* => *, Tuple2, Either]]
  summon[DistributiveK[* => *, /\, \/]]

  trait LensK[S[_], A[_]]() { self =>
    def get[x]: S[x] => A[x]
    def set[x]: (S[x], A[x]) => S[x]
    
    def andThen[B[_]](that: LensK[A, B]): LensK[S, B] = new LensK[S, B] {
      def get[x]: S[x] => B[x] = s => that.get(self.get(s))
      def set[x]: (S[x], B[x]) => S[x] = (s, b) => self.set(s, that.set(self.get(s), b))
    }
  }

  trait Algebra[F[_], A, B] {
    def blah1[X](a: X): F[X]
    def blah2(i: Int): F[String]
    def blah3(f: F[A]): F[B]
  }

//  def algMap[F[_], G[_]]()

  type Algebra1[F[_]] = Algebra[F[_], Int, String]


}
