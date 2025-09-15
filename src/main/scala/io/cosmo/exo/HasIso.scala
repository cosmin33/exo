package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import scala.compiletime.summonFrom

opaque type HasIso[->[_,_], A, B] <: Iso[->, A, B] = Iso[->, A, B]

object HasIso extends HasIsoImplicits:
  def apply[->[_,_], A, B](i: Iso[->, A, B]): HasIso[->, A, B] = i

  given first[->[_,_], A, B](using e: EqImpIso[->, A, B]): HasIso[->, A, B] = e

private[exo] trait HasIsoImplicits extends HasIsoImplicits01:
  given second[->[_,_], A, B](using i: Iso[->, A, B]): HasIso[->, A, B] = HasIso(i)

private[exo] trait HasIsoImplicits01:
  given third[->[_,_], A, B](using i: Iso[->, B, A]): HasIso[->, A, B] = HasIso(i.flip)

private[exo] opaque type ReflImpIso[->[_,_], A] = Iso[->, A, A]

private[exo] object ReflImpIso:
  given[->[_,_], A](using SubcatHasId[->, A]): ReflImpIso[->, A] = Iso.refl[->, A]

private[exo] opaque type EqImpIso[->[_,_], A, B] = Iso[->, A, B]

private[exo] object EqImpIso:
  given[->[_,_], A, B](using eq: A === B, r: ReflImpIso[->, A]): EqImpIso[->, A, B] = eq.subst(r)

