package io.cosmo.exo.typeclasses

import io.cosmo.exo.{<=>, Iso}
import io.cosmo.exo.evidence.{===, =~=, Is}

trait HasTypeclass[TC, TF] {
  type C[_[_]]
  type F[_]
  def leib1: TC === TypeH[C]
  def leib2: TF === TypeF[F]
  def instance: C[F]
}
object HasTypeclass {
  type Aux1[TC, TF, CC[_[_]]]        = HasTypeclass[TC, TF] {type C[f[_]] = CC[f]}
  type Aux2[TC, TF, C0[_[_]], F0[_]] = HasTypeclass[TC, TF] {type C[f[_]] = C0[f]; type F[a] = F0[a]}

  implicit def steal[C0[_[_]], F0[_]](implicit source: C0[F0]): HasTypeclass.Aux2[TypeH[C0], TypeF[F0], C0, F0] =
    new HasTypeclass[TypeH[C0], TypeF[F0]] {
      type C[f[_]] = C0[f]
      type F[a] = F0[a]
      val leib1 = Is.refl
      val leib2 = Is.refl
      val instance: C[F] = source
    }

  def isoCanonic[C[_[_]], F[_]]: C[F] <=> HasTypeclass[TypeH[C], TypeF[F]] =
    {
      val rr: C[F] <=> HasTypeclass[TypeH[C], TypeF[F]] =
        Iso.unsafe(
          HasTypeclass.steal(_),
          h => {
            val ff: F =~= h.F = TypeF.injectivity(h.leib2)
              //.subst(h.instance)
            ???
          }
        )

      ???
    }

}
