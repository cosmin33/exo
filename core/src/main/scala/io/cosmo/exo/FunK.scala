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
  def apply[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] = forallFr.of[F, G](fn)

  private def applyFrom[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] =
    new FunK[TypeF[F], TypeF[G]] {
      type TypeA[x] = F[x]
      type TypeB[x] = G[x]
      val eqA = Is.refl
      val eqB = Is.refl
      def instance = fn
    }
  val forallFr = ForallKBi.of[λ[(f[_],g[_]) => (f ~> g) => FunK[TypeF[f], TypeF[g]]]](applyFrom)

  private def applyTo[F[_], G[_]](fk: FunK[TypeF[F], TypeF[G]]): F ~> G = {
    val i1: fk.TypeA =~= F = TypeF.injectivity(fk.eqA)
    val i2: fk.TypeB =~= G = TypeF.injectivity(fk.eqB)
    val eq: (fk.TypeA ~> fk.TypeB) === (F ~> G) = i1.lower2[~>](i2)
    eq(fk.instance)
  }
  val forallTo = ForallKBi.of[λ[(f[_],g[_]) => FunK[TypeF[f], TypeF[g]] => (f ~> g)]].from(applyTo)

  implicit class FunKOps[F[_], G[_]](val self: FunK[TypeF[F], TypeF[G]]) extends AnyVal {
    def unwrap: F ~> G = forallTo.apply(self)
    def apply[A](fa: F[A]): G[A] = unwrap[A](fa)
  }

  implicit def isoCanonic[F[_], G[_]]: FunK[TypeF[F], TypeF[G]] <=> ~>[F, G] =
    Iso.unsafe(forallTo[F, G], forallFr[F, G])

  implicit def conversion[F[_], G[_]](fn: F ~> G): FunK[TypeF[F], TypeF[G]] = forallFr.of[F, G](fn)

  implicit def categ: Subcat.Aux[FunK, IsTypeF] =
    new Subcat[FunK] {
      type TC[a] = IsTypeF[a]

//      def id[A](implicit tc: IsTypeF[A]) = apply(∀.mk[tc.Type ~> tc.Type].from(a => a))

      def id[A](implicit tc: IsTypeF[A]) = new FunK[A, A] {
        type T[a] = tc.Type[a]
        type TypeA[x] = T[x]
        type TypeB[x] = T[x]
        def eqA: TypeF[T] === A = tc.eq
        def eqB: TypeF[T] === A = tc.eq
        def instance = ∀.mk[T ~> T].from(a => a)
      }

      override def andThen[A, B, C](ab: FunK[A, B], bc: FunK[B, C]) =
        new FunK[A, C] {
          type TypeA[x] = ab.TypeA[x]
          type TypeB[x] = bc.TypeB[x]
          def eqA = ab.eqA
          def eqB = bc.eqB
          def instance = ∀.mk[TypeA ~> TypeB].from(
            TypeF.injectivity(ab.eqB.andThen(bc.eqA.flip))
              .subst(ab.instance).apply
              .andThen(bc.instance.apply)
          )
        }
    }

}