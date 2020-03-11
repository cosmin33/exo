package io.cosmo.exo

import io.cosmo.exo.categories.{Dual, Opp, Subcat}
import io.cosmo.exo.evidence.{===, =~=, Is, IsK2}
import io.cosmo.exo.typeclasses.{IsTypeF, TypeF}

trait FunK[TA, TB] {
  type TypeA[_]
  type TypeB[_]
  def eqA: TypeF[TypeA] === TA
  def eqB: TypeF[TypeB] === TB
  def instance: TypeA ~> TypeB
}
object FunK {
  def apply[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] = wrap(fn)

  private def wrap[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] =
    new FunK[TypeF[F], TypeF[G]] {
      type TypeA[x] = F[x]
      type TypeB[x] = G[x]
      val eqA = Is.refl
      val eqB = Is.refl
      def instance = fn
    }

  private def unwrap[F[_], G[_]](fk: FunK[TypeF[F], TypeF[G]]): F ~> G = {
    val i1: fk.TypeA =~= F = TypeF.injectivity(fk.eqA)
    val i2: fk.TypeB =~= G = TypeF.injectivity(fk.eqB)
    val eq: (fk.TypeA ~> fk.TypeB) === (F ~> G) = i1.lower2[~>](i2)
    eq(fk.instance)
  }

  implicit class FunKOps[F[_], G[_]](val self: FunK[TypeF[F], TypeF[G]]) extends AnyVal {
    def unwrap: F ~> G = FunK.unwrap(self)
    def apply[A](fa: F[A]): G[A] = unwrap[A](fa)
  }

  implicit def isoCanonic[F[_], G[_]]: FunK[TypeF[F], TypeF[G]] <=> (F ~> G) =
    Iso.unsafe(unwrap[F, G], wrap[F, G])

  implicit def isoKIso[F[_], G[_]]: Iso[FunK, TypeF[F], TypeF[G]] <=> (F <~> G) =
    Iso.unsafe(
      iso => <~>.unsafe(iso.to.unwrap, iso.from.unwrap),
      fig => Iso.unsafe(FunK(fig.toK), FunK(fig.fromK))
    )

  implicit def isoKIsoFunK[F[_], G[_]](implicit i: F <~> G): Iso[FunK, TypeF[F], TypeF[G]] = isoKIso[F, G].from(i)

  //implicit def isoKConversion[F[_], G[_]](i: F <~> G): Iso[FunK, TypeF[F], TypeF[G]] = isoKIso[F, G].from(i)

  //implicit def conversion[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] = wrap(fn)

  implicit def categ: Subcat.Aux[FunK, IsTypeF] =
    new Subcat[FunK] {
      type TC[a] = IsTypeF[a]

      def id[A](implicit tc: IsTypeF[A]): FunK[A, A] =
        Is.lift2[FunK](tc.is, tc.is)(FunK(∀.mk[tc.Type ~> tc.Type].from(a => a)))

      override def andThen[A, B, C](ab: FunK[A, B], bc: FunK[B, C]): FunK[A, C] = new FunK[A, C] {
        type TypeA[x] = ab.TypeA[x]
        type TypeB[x] = bc.TypeB[x]
        val (eqA, eqB) = (ab.eqA, bc.eqB)
        val instance = ∀.mk[TypeA ~> TypeB].from(
          TypeF.injectivity(ab.eqB.andThen(bc.eqA.flip))
            .subst(ab.instance).apply
            .andThen(bc.instance.apply))
      }
    }

}