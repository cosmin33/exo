package io.cosmo.exo

/** SingleOf[T, U] represents an implicit value of type T narrowed to its singleton type U.
 * Technique from Miles Sabin's gist: https://gist.github.com/milessabin/cadd73b7756fe4097ca0 */
case class SingleOf[T, U](value: U)
object SingleOf {
  implicit def mkSingleOf[T <: AnyRef](implicit t: T): SingleOf[T, t.type] = SingleOf(t)
}
