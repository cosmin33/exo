package io.cosmo.exo.evidence

import io.cosmo.exo.*
import io.cosmo.exo.inhabitance.*

sealed abstract class StrictAs[-A, +B] { ab =>

  def inequality[A1 <: A, B1 >: B]: A1 =!= B1

  def conformity: A <~< B

  def contradicts(ba: B <~< A): Void = inequality[A, B].run(Axioms.bracket(ab.conformity, ba))

  /** Substitution into a covariant context. */
  def substCo[F[+_]](fa: F[A]): F[B] = conformity.substCv[F](fa)

  /** Substitution into a contravariant context. */
  def substCt[F[-_]](fb: F[B]): F[A] = conformity.substCt[F](fb)

  /** Substitution on identity brings about a direct coercion function of the same form that [[<:<]] provides. */
  final def apply(a: A): B = coerce(a)

  def andThen[A1 <: A, C](bc: B </< C): A1 </< C = bc.conformity.substCv[[x] =>> StrictAs[A1, x]](ab)

  def compose[Z, B1 >: B](za: Z </< A): Z </< B1 = za andThen ab

  def andThenNS[A1 <: A, C](bc: B <~< C): A1 </< C = bc.substCv[[x] =>> StrictAs[A1, x]](ab)

  def composeNS[Z, B1 >: B](za: Z <~< A): Z </< B1 = za.substCt[[x] =>> StrictAs[x, B1]](ab)

  /** Substitution on identity brings about a direct coercion function of the same form that [[<:<]] provides. */
  final def coerce(a: A): B = substCo[[x] =>> x](a)

  /** Given `A <~< B` we can prove that `F[A] <~< F[B]` for any covariant `F[+_]`. */
  final def liftCoNS[F[+_]]: F[A] <~< F[B] = substCo[[x] =>> F[A] <~< F[x]](As.refl[F[A]])

  /** Given `A <~< B` we can prove that `F[A] <~< F[B]` for any contravariant `F[-_]`. */
  final def liftCtNS[F[-_]]: F[B] <~< F[A] = substCo[[x] =>> F[x] <~< F[A]](As.refl)

}
object StrictAs {
  def apply[A, B](implicit ev: A </< B): A </< B = ev

  private[this] final class Witness[A, B](val nab: A =!= B, val conformity: A <~< B) extends StrictAs[A, B] {
    def inequality[A1 <: A, B1 >: B]: A1 =!= B1 =
      WeakApart.witness { a1b1 =>
        val nc: B1 <~< A1 = a1b1.flip.toAs
        nab.run(Axioms.bracket(conformity, nc : As[B, A]))
      }
  }

  implicit def isoCanonic[A, B]: (A =!= B, A <~< B)  <=> (A </< B) =
    Iso.unsafe({case (nb, ab) => witness(nb, ab)}, c => (c.inequality, c.conformity))

  implicit def witness[A, B](implicit nab: A =!= B, conformity: A <~< B): StrictAs[A, B] =
    new Witness[A, B](nab, conformity)

  def witnessNot[A, B](implicit ev: ¬¬[¬[A <~< B] Either (A === B)]): ¬[A </< B] =
    Uninhabited.witness((sab: A </< B) => ev {
      case Right(ab) => sab.inequality[A, B].run(ab)
      case Left(nab) => nab(sab.conformity)
    })

  def bottomTop: Void </< Any = witness(Void.isNotAny, As.bottomTop)

  def irreflexive[A](ev: A </< A): Void =
    ev.inequality[A, A].run(Is.refl)

  implicit def strictAsIsProposition[A, B]: Proposition[StrictAs[A, B]] =
    Proposition[A =!= B].zip(using Proposition[A <~< B]).isomap(Iso.unsafe(
      p => witness(p._1, p._2),
      p => (p.inequality[A, B], p.conformity)
    ))

}
