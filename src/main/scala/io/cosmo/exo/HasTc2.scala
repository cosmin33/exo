package io.cosmo.exo

sealed trait HasTc2[TC[_[_,_]], TF]:
  type F[_,_]
  def isk: IsKind2.Aux[TF, F]
  def instance: TC[F]
  def instanceFor(i: IsKind2[TF]): TC[i.Type] = IsKind2.injectivity(isk, i).subst[TC](instance)

object HasTc2 {
  type Aux[TC[_[_,_]], TF, F0[_,_]] = HasTc2[TC, TF] {type F[a, b] = F0[a, b]}

  private[this] def from[TC[_[_,_]], F0[_,_], A](tc: TC[F0], i: IsKind2.Aux[A, F0]): HasTc2.Aux[TC, A, F0] =
    new HasTc2[TC, A] { type F[a, b] = F0[a, b]; val isk = i; val instance = tc }

  def apply[TC[_[_,_]], F[_,_]](tc: TC[F]): HasTc2.Aux[TC, TypeK2[F], F] = from(tc, IsKind2.impl[F])

  given instance[TC[_[_,_]], F[_,_]](using tc: TC[F]): HasTc2.Aux[TC, TypeK2[F], F] = apply(tc)

  given isoCanonic[TC[_[_,_]], A](using i: IsKind2[A]): (HasTc2[TC, A] <=> TC[i.Type]) =
    Iso.unsafe(ht => IsKind2.injectivity(ht.isk, i).subst[TC](ht.instance), from(_, i))

  given isoFun[TC[_[_,_]], A, F[_,_], B, G[_,_]](using
    ia: IsKind2.Aux[A, F], ib: IsKind2.Aux[B, G]
  ): ((HasTc2[TC, A] => HasTc2[TC, B]) <=> (TC[F] => TC[G])) =
    val i1 = isoCanonic[TC, A]
    val i2 = isoCanonic[TC, B]
    Iso.unsafe(i1.from andThen _ andThen i2.to, i1.to andThen _ andThen i2.from)

  given isoIso[TC[_[_,_]], A, F[_,_], B, G[_,_]](using
    ia: IsKind2.Aux[A, F], ib: IsKind2.Aux[B, G]
  ): ((HasTc2[TC, A] <=> HasTc2[TC, B]) <=> (TC[F] <=> TC[G])) =
    val i1 = isoCanonic[TC, A]
    val i2 = isoCanonic[TC, B]
    Iso.unsafe(i1.flip andThen _ andThen i2, i1 andThen _ andThen i2.flip)

}
