package io.cosmo.exo

import io.estatico.newtype.Coercible

trait coercible {

  implicit def isoCoercible[F[_], G[_]]: ∀[λ[a => Coercible[F[a], G[a]]]] <=> Coercible[∀[F], ∀[G]] =
    Iso.unsafeT(
      _ => Coercible.instance,
      _ => ∀.of[λ[a => Coercible[F[a], G[a]]]].from(Coercible.instance)
    )
  implicit def isoCoercible2[F[_,_], G[_,_]]: ∀∀[λ[(a,b) => Coercible[F[a,b], G[a,b]]]] <=> Coercible[∀∀[F], ∀∀[G]] =
    Iso.unsafeT(
      _ => Coercible.instance,
      _ => ∀∀.of[λ[(a,b) => Coercible[F[a,b], G[a,b]]]].from(Coercible.instance),
    )

}

object coercible extends coercible
