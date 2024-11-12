package io.cosmo.exo

/** Witness for a given F[_] that there exists a given TC[F] instance. */
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

  given isoCanonic[TC[_[_]], A](using i: IsKind[A]): (HasTc[TC, A] <=> TC[i.Type]) =
    Iso.unsafe(ht => IsKind.injectivity(ht.isk, i).subst[TC](ht.instance), from(_, i))

  given isoFun[TC[_[_]], A, F[_], B, G[_]](using
    ia: IsKind.Aux[A, F], ib: IsKind.Aux[B, G]
  ): ((HasTc[TC, A] => HasTc[TC, B]) <=> (TC[F] => TC[G])) =
    val i1 = isoCanonic[TC, A]
    val i2 = isoCanonic[TC, B]
    Iso.unsafe(i1.from andThen _ andThen i2.to, i1.to andThen _ andThen i2.from)

  def isoFun1[TC[_[_]], A, F[_], B, G[_]](using
    ia: IsKind.Aux[A, F], ib: IsKind.Aux[B, G]
  ): ((TC[F] => TC[G]) <=> (HasTc[TC, A] => HasTc[TC, B])) =
    val i1 = isoCanonic[TC, A]
    val i2 = isoCanonic[TC, B]
    Iso.unsafe(i1.to andThen _ andThen i2.from, i1.from andThen _ andThen i2.to)

  given isoIso[TC[_[_]], A, F[_], B, G[_]](using
    ia: IsKind.Aux[A, F], ib: IsKind.Aux[B, G]
  ): ((HasTc[TC, A] <=> HasTc[TC, B]) <=> (TC[F] <=> TC[G])) =
    val i1 = isoCanonic[TC, A]
    val i2 = isoCanonic[TC, B]
    Iso.unsafe(i1.flip andThen _ andThen i2, i1 andThen _ andThen i2.flip)
end HasTc
