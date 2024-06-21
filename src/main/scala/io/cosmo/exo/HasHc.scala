package io.cosmo.exo

/** Witness for a given A[_[_]] that there exists a given TC[A] instance. */
sealed trait HasHc[TC[_[_[_]]], TF]:
  type F[_[_]]
  def isk: IsHKind.Aux[TF, F]
  def instance: TC[F]
  def instanceFor(i: IsHKind[TF]): TC[i.Type] = IsHKind.injectivity(isk, i).subst[TC](instance)

object HasHc:
  type Aux[TC[_[_[_]]], TF, F0[_[_]]] = HasHc[TC, TF] { type F[a[_]] = F0[a] }

  private[this] def from[TC[_[_[_]]], F0[_[_]], A](tc: TC[F0], i: IsHKind.Aux[A, F0]): HasHc.Aux[TC, A, F0] =
    new HasHc[TC, A] { type F[a[_]] = F0[a]; val isk = i; val instance = tc }

  def apply[TC[_[_[_]]], F[_[_]]](tc: TC[F]): HasHc.Aux[TC, TypeHK[F], F] = from(tc, IsHKind.impl[F])

  given instance[TC[_[_[_]]], F[_[_]]](using tc: TC[F]): HasHc.Aux[TC, TypeHK[F], F] = apply(tc)

  given isoCanonic[TC[_[_[_]]], A](using i: IsHKind[A]): (HasHc[TC, A] <=> TC[i.Type]) =
    Iso.unsafe(ht => IsHKind.injectivity(ht.isk, i).subst[TC](ht.instance), from(_, i))

  given isoFun[TC[_[_[_]]], A, F[_[_]], B, G[_[_]]](using
    ia: IsHKind.Aux[A, F], ib: IsHKind.Aux[B, G]
  ): ((HasHc[TC, A] => HasHc[TC, B]) <=> (TC[F] => TC[G])) =
    val i1 = isoCanonic[TC, A]
    val i2 = isoCanonic[TC, B]
    Iso.unsafe(i1.from andThen _ andThen i2.to, i1.to andThen _ andThen i2.from)

  given isoIso[TC[_[_[_]]], A, F[_[_]], B, G[_[_]]](using
    ia: IsHKind.Aux[A, F], ib: IsHKind.Aux[B, G]
  ): ((HasHc[TC, A] <=> HasHc[TC, B]) <=> (TC[F] <=> TC[G])) =
    val i1 = isoCanonic[TC, A]
    val i2 = isoCanonic[TC, B]
    Iso.unsafe(i1.flip andThen _ andThen i2, i1 andThen _ andThen i2.flip)
  
end HasHc
