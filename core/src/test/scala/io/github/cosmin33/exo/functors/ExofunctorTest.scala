package io.github.cosmin33.exo.functors

import io.github.cosmin33.exo.evidence.*
import io.github.cosmin33.exo.*

object ExofunctorTest {

  def liskov1[F[_]]: Exo[===, ===, F] = summon
  def liskov2[F[_]]: Exo[===, <~<, F] = summon
  def liskov3[F[_]]: Exo[===, * => *, F] = summon
  def liskov4[F[_]]: Exo[===, <=>, F] = summon

}
