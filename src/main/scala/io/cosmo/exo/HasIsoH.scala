package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*

private[exo] opaque type ReflImpIsoH[->[_,_], F[_[_]]] = IsoH[->, F, F]
private[exo] object ReflImpIsoH:
  given impl[->[_,_], F[_[_]]](using s: SubcategoryH[->], tc: s.TC[F]): ReflImpIsoH[->, F] =
    IsoH.refl[->, F](using SubcatHHasId.from(using s, tc))

private[exo] opaque type EqImpIsoH[->[_,_], F[_[_]], G[_[_]]] = IsoH[->, F, G]
private[exo] object EqImpIsoH:
  given impl[->[_,_], F[_[_]], G[_[_]]](using eq: F =≈= G, r: ReflImpIsoH[->, F]): EqImpIsoH[->, F, G] =
    eq.subst[[f[_[_]]] =>> IsoH[->, F, f]](r: IsoH[->, F, F])

opaque type HasIsoH[->[_,_], F[_[_]], G[_[_]]] <: IsoH[->, F, G] = IsoH[->, F, G]
object HasIsoH:
  given impl[->[_,_], F[_[_]], G[_[_]]](using e: EqImpIsoH[->, F, G] \/ (IsoH[->, F, G] \/ IsoH[->, G, F])): HasIsoH[->, F, G] =
    e.fold3(identity, identity, _.flipH)
