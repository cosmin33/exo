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

  /** TypeF is injective so
   *   if two TypeF's are equal then the types contained are equal. */
  def injectivity[F[_], G[_]](ev: TypeF[F] === TypeF[G]): F =~= G = Unsafe.isK[F, G]
}

trait IsTypeF[A] {
  type Type[a]
  def eq: TypeF[Type] === A
}
object IsTypeF {
  type Aux[A, F[_]] = IsTypeF[A] {type Type[a] = F[a]}

  val forall = ForallK.of[λ[k[_] => IsTypeF[TypeF[k]]]](new IsTypeFImpl)
  private final class IsTypeFImpl[F[_]] extends IsTypeF[TypeF[F]] {
    type Type[a] = F[a]
    def eq = Is.refl
  }

  implicit def impl[K[_]]: IsTypeF[TypeF[K]] = forall[K]

  type FF[F[_], a] = IsTypeF[TypeF[F]]#Type[a]

  def someStupidRel[F[_], x]: F[x] <~< FF[F, x] = {
    val ist: IsTypeF[TypeF[F]] = impl[F]
    def s1[A]: F[A] <~< ist.Type[A] = TypeF.injectivity(ist.eq.flip).is[A].toAs
    def s2[A] = the[ist.Type[A] <~< FF[F, A]]
    def za[A]: F[A] <~< FF[F, A] = s1.andThen(s2)
    //def j1[A] = <~<[FF[F, A], ist.H[A]]
    
    za[x]
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