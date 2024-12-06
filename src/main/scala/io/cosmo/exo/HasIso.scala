package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import scala.compiletime.summonFrom

opaque type HasIso[->[_, _], A, B] <: Iso[->, A, B] = Iso[->, A, B]

object HasIso:
  given[->[_, _], A, B](using e: EqImpIso[->, A, B] \/ (Iso[->, A, B] \/ Iso[->, B, A])): HasIso[->, A, B] =
    e.fold3(identity, identity, _.flip)

private[exo] opaque type ReflImpIso[->[_, _], A] = Iso[->, A, A]

private[exo] object ReflImpIso:
  given[->[_, _], A](using SubcatHasId[->, A]): ReflImpIso[->, A] = Iso.refl[->, A]

private[exo] opaque type EqImpIso[->[_, _], A, B] = Iso[->, A, B]

private[exo] object EqImpIso:
  given[->[_, _], A, B](using eq: A === B, r: ReflImpIso[->, A]): EqImpIso[->, A, B] = eq.subst(r)

