package io.cosmo.exo.functors

import io.cosmo.exo.evidence.*
import io.cosmo.exo.*

object ExofunctorTest {

  def liskov1[F[_]]: Exo[===, ===, F] = summon
  def liskov2[F[_]]: Exo[===, <~<, F] = summon
  def liskov3[F[_]]: Exo[===, * => *, F] = summon
  def liskov4[F[_]]: Exo[===, <=>, F] = summon

}
