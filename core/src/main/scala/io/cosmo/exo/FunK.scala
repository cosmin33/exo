package io.cosmo.exo

import io.cosmo.exo.categories.{Dual, Opp, Subcat}
import io.cosmo.exo.evidence.{===, =~=, Is}
import io.cosmo.exo.typeclasses.{IsTypeF, TypeF}

trait FunK[TA, TB] {
  type TypeA[_]
  type TypeB[_]
  def eqA: TypeF[TypeA] === TA
  def eqB: TypeF[TypeB] === TB
  def instance: TypeA ~> TypeB
}
object FunK {
  def apply[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] = faWrap.of[F, G](fn)

  private def wrapProto[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] =
    new FunK[TypeF[F], TypeF[G]] {
      type TypeA[x] = F[x]
      type TypeB[x] = G[x]
      val eqA = Is.refl
      val eqB = Is.refl
      def instance = fn
    }
  private def unwrapProto[F[_], G[_]](fk: FunK[TypeF[F], TypeF[G]]): F ~> G = {
    val i1: fk.TypeA =~= F = TypeF.injectivity(fk.eqA)
    val i2: fk.TypeB =~= G = TypeF.injectivity(fk.eqB)
    val eq: (fk.TypeA ~> fk.TypeB) === (F ~> G) = i1.lower2[~>](i2)
    eq(fk.instance)
  }
  private val faWrap   = ForallKBi.of[λ[(f[_],g[_]) => (f ~> g) => FunK[TypeF[f], TypeF[g]]]](wrapProto)
  private val faUnwrap = ForallKBi.of[λ[(f[_],g[_]) => FunK[TypeF[f], TypeF[g]] => (f ~> g)]](unwrapProto)

  implicit class FunKOps[F[_], G[_]](val self: FunK[TypeF[F], TypeF[G]]) extends AnyVal {
    def unwrap: F ~> G = faUnwrap.apply(self)
    def apply[A](fa: F[A]): G[A] = unwrap.of[A](fa)
  }

  implicit def isoCanonic[F[_], G[_]]: FunK[TypeF[F], TypeF[G]] <=> ~>[F, G] =
    Iso.unsafe(faUnwrap[F, G], faWrap[F, G])

  implicit def isoKIso[F[_], G[_]]: Iso[FunK, TypeF[F], TypeF[G]] <=> (F <~> G) =
    Iso.unsafe(
      iso => <~>.unsafe(iso.to.unwrap, iso.from.unwrap),
      fig => Iso.unsafe(FunK(fig.to), FunK(fig.from)))

  def isoKConversion[F[_], G[_]](i: F <~> G): Iso[FunK, TypeF[F], TypeF[G]] = isoKIso[F, G].from(i)

  implicit def conversion[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] = faWrap.of[F, G](fn)

  implicit def categ: Subcat.Aux[FunK, IsTypeF] =
    new Subcat[FunK] {
      type TC[a] = IsTypeF[a]

      def id[A](implicit tc: IsTypeF[A]): FunK[A, A] =
        Is.lift2[FunK](tc.is, tc.is)(FunK(∀.mk[tc.Type ~> tc.Type].from(a => a)))

      private[this] def andThenProto[A, B, C](ab: FunK[A, B], bc: FunK[B, C]) =
        new FunK[A, C] {
          type TypeA[x] = ab.TypeA[x]
          type TypeB[x] = bc.TypeB[x]
          val (eqA, eqB) = (ab.eqA, bc.eqB)
          val instance = ∀.mk[TypeA ~> TypeB].from(
            TypeF.injectivity(ab.eqB.andThen(bc.eqA.flip))
              .subst(ab.instance).apply
              .andThen(bc.instance.apply))
        }
      val faAndThen = ∀∀∀.of[λ[(a,b,c) => (FunK[a,b], FunK[b,c]) => FunK[a,c]]](andThenProto(_,_))

      override def andThen[A, B, C](ab: FunK[A, B], bc: FunK[B, C]): FunK[A, C] = faAndThen.of(ab, bc)
    }

}