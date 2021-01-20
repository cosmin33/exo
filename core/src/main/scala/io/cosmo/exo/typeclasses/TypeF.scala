package io.cosmo.exo.typeclasses

import io.cosmo
import io.cosmo.exo
import io.cosmo.exo.evidence._
import io.cosmo.exo._
import io.cosmo.exo.evidence.internal.Unsafe
import shapeless.the

sealed abstract class TypeF[F[_]]

object TypeF {
  def apply[F[_]]: TypeF[F] = forall.apply[F]

  val forall: ForallK[TypeF] = ForallK.of[TypeF].fromH(f => new TypeF[f.T] {})

  implicit def impl: ForallK[TypeF] = forall

  /** TypeF is injective, so if two TypeF's are equal then the types contained are equal. */
  def injectivity[F[_], G[_]](implicit ev: TypeF[F] === TypeF[G]): F =~= G = Unsafe.isK[F, G]
}

trait IsTypeF[A] {
  type Type[a]
  def is: TypeF[Type] === A
  //def iso: TypeF[Type] <=> A
}
object IsTypeF {
  def apply[F[_]]: IsTypeF[TypeF[F]] = impl[F]
  type Aux[A, F[_]] = IsTypeF[A] {type Type[a] = F[a]}

  implicit def impl[F[_]]: IsTypeF[TypeF[F]] = new IsTypeF[TypeF[F]] {
    type Type[a] = F[a]
    def is = Is.refl
  }

  def prod[F[_], G[_]]: TypeF[λ[a => (F[a], G[a])]] <=> (TypeF[F], TypeF[G]) =
    Iso.unsafe(
      _ => (TypeF[F], TypeF[G]),
      _ => TypeF[λ[a => (F[a], G[a])]]
    )

  def coprod[F[_], G[_]]: TypeF[λ[a => Either[F[a], G[a]]]] <=> Either[TypeF[F], TypeF[G]] =
    Iso.unsafe(
      t => ???,
      _ => TypeF[λ[a => Either[F[a], G[a]]]]
    )

  type FF[F[_], a] = IsTypeF[TypeF[F]]#Type[a]

  def someStupidRel[F[_], X]: F[X] <~< FF[F, X] = {
    val ist: IsTypeF[TypeF[F]] = IsTypeF[F]
//    def s1[A]: F[A] <~< ist.Type[A] = TypeF.injectivity[F, ist.Type].is[A].toAs
    def s1[A]: F[A] <~< ist.Type[A] = TypeF.injectivity(ist.is.flip).is[A].toAs
    def s2[A] = <~<[ist.Type[A], FF[F, A]]
    s1.andThen(s2)
  }
}

sealed abstract class TypeH[H[_[_]]]

object TypeH {
  def apply[H[_[_]]]: TypeH[H] = new TypeH[H] {}
  //def injectivity[H[_[_]], J[_[_]]](ev: TypeH[H] === TypeH[J]): ForallK[λ[f[_] => H[f] === J[f]]] = ???
}

trait IsTypeH[A] {
  type Type[f[_]]
  def eq: TypeH[Type] === A
}
object IsTypeH {
  type Aux[A, H[_[_]]] = IsTypeH[A] {type Type[f[_]] = H[f]}

  implicit def impl[H[_[_]]]: IsTypeH[TypeH[H]] = new IsTypeH[TypeH[H]] {
    type Type[f[_]] = H[f]
    def eq = Is.refl
  }
}