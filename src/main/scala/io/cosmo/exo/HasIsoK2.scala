package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*

private[exo] opaque type ReflImpIsoK2[->[_,_], F[_,_]] = IsoK2[->, F, F]
private[exo] object ReflImpIsoK2:
  given impl[->[_,_], F[_,_]](using s: SubcategoryK2[->], tc: s.TC[F]): ReflImpIsoK2[->, F] =
    IsoK2.refl[->, F](using SubcatK2HasId.from(using s, tc))

private[exo] opaque type EqImpIsoK2[->[_,_], F[_,_], G[_,_]] = IsoK2[->, F, G]
private[exo] object EqImpIsoK2:
  given impl[->[_,_], F[_,_], G[_,_]](using eq: F =~~= G, r: ReflImpIsoK2[->, F]): EqImpIsoK2[->, F, G] =
    eq.subst[[f[_,_]] =>> IsoK2[->, F, f]](r: IsoK2[->, F, F])

opaque type HasIsoK2[->[_,_], F[_,_], G[_,_]] <: IsoK2[->, F, G] = IsoK2[->, F, G]
object HasIsoK2:
  given impl[->[_,_], F[_,_], G[_,_]](using e: EqImpIsoK2[->, F, G] \/ (IsoK2[->, F, G] \/ IsoK2[->, G, F])): HasIsoK2[->, F, G] =
    e.fold3(identity, identity, _.flip)
