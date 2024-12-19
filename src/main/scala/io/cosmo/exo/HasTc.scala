package io.cosmo.exo

/** Witness for `F[_]` that there is a stored `TC[F]` instance. `F[_]` is computed by `IsKind.Aux[TF, F]` */
sealed trait HasTc[TC[_[_]], TF]:
  type F[_]
  def isk: IsKind.Aux[TF, F]
  def instance: TC[F]
  def instanceFor(i: IsKind[TF]): TC[i.Type] = IsKind.injectivity(isk, i).subst[TC](instance)

object HasTc:
  type Aux[TC[_[_]], TF, F0[_]] = HasTc[TC, TF] { type F[a] = F0[a] }

  private[this] def from[TC[_[_]], F0[_], A](tc: TC[F0], i: IsKind.Aux[A, F0]): HasTc.Aux[TC, A, F0] =
    new HasTc[TC, A] { type F[a] = F0[a]; val isk = i; val instance = tc }

  def apply[TC[_[_]], F[_]](tc: TC[F]): HasTc.Aux[TC, TypeK[F], F] = from(tc, IsKind.impl[F])
  
  def unapply[TC[_[_]], F[_]](ht: HasTc[TC, TypeK[F]]): TC[F] = ht.instanceFor(IsKind.impl[F])

  given instance[TC[_[_]], F[_]](using tc: TC[F]): HasTc.Aux[TC, TypeK[F], F] = apply(tc)

  given isoCanonic[TC[_[_]], A](using i: IsKind[A]): (TC[i.Type] <=> HasTc[TC, A]) =
    Iso.unsafe(from(_, i), ht => IsKind.injectivity(ht.isk, i).subst[TC](ht.instance))

  given isoFun[TC[_[_]], A, F[_], B, G[_]](using
    ia: IsKind.Aux[A, F], ib: IsKind.Aux[B, G]
  ): ((TC[F] => TC[G]) <=> (HasTc[TC, A] => HasTc[TC, B])) =
    val i1: TC[F] <=> HasTc[TC, A] = isoCanonic
    val i2: TC[G] <=> HasTc[TC, B] = isoCanonic
    Iso.unsafe(i1.from andThen _ andThen i2.to, i1.to andThen _ andThen i2.from)
  
  given isoIso[TC[_[_]], A, F[_], B, G[_]](using
    ia: IsKind.Aux[A, F], ib: IsKind.Aux[B, G]
  ): ((TC[F] <=> TC[G]) <=> (HasTc[TC, A] <=> HasTc[TC, B])) =
    val i1: TC[F] <=> HasTc[TC, A] = isoCanonic
    val i2: TC[G] <=> HasTc[TC, B] = isoCanonic
    Iso.unsafe(i1.flip andThen _ andThen i2, i1 andThen _ andThen i2.flip)
end HasTc
