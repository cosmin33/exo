package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*

private[exo] opaque type ReflImpIsoK[->[_,_], F[_]] = IsoK[->, F, F]
private[exo] object ReflImpIsoK:
  given impl[->[_,_], F[_]](using s: SubcategoryK[->], tc: s.TC[F]): ReflImpIsoK[->, F] =
    IsoK.refl[->, F](using SubcatKHasId.from(using s, tc))

private[exo] opaque type EqImpIsoK[->[_,_], F[_], G[_]] = IsoK[->, F, G]
private[exo] object EqImpIsoK:
  given impl[->[_,_], F[_], G[_]](using eq: F =~= G, r: ReflImpIsoK[->, F]): EqImpIsoK[->, F, G] =
    eq.subst[[f[_]] =>> IsoK[->, F, f]](r: IsoK[->, F, F])

opaque type HasIsoK[->[_,_], F[_], G[_]] <: IsoK[->, F, G] = IsoK[->, F, G]
object HasIsoK:
  given impl[->[_,_], F[_], G[_]](using e: EqImpIsoK[->, F, G] \/ (IsoK[->, F, G] \/ IsoK[->, G, F])): HasIsoK[->, F, G] =
    e.fold3(identity, identity, _.flipK)
