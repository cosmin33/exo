package io.cosmo.exo.inhabitance

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*

opaque type Uninhabited[A] <: A => Void = A => Void

object Uninhabited {
  def apply[A](implicit ev: ¬[A]): ¬[A] = ev

  def witness[A](f: A => Void): ¬[A] = eqCanonic(f)

  extension [A](self: ¬[A])
    def contradicts(a: A): Void = self(a)
    def notInhabited(a: ¬¬[A]): Void = a.contradicts(self)
    def contramap[B](f: B => A): ¬[B] = witness(b => self(f(b))) //witness(f >>> self.run)
    def zip[B](notB: ¬[B]): ¬[Either[A, B]] = witness[Either[A, B]](_.fold(self, notB))

  def eqCanonic [A]: (A => Void) === ¬[A] = summon[(A => Void) === ¬[A]]

  def isoCanonic[A]: (A => Void) <=> ¬[A] = Iso.refl[¬[A]]

  def contramap2[A, B, C](p: ¬¬[Either[¬[A], ¬[B]]])(f: C => (A, B)): ¬[C] =
    witness { c =>
      val (a, b) = f(c)
      p.contradicts {
        case Left(notA) => notA.contradicts(a)
        case Right(notB) => notB.contradicts(b)
      }
    }

  def codivide[A, B, C](p: ¬¬[(¬[A], ¬[B])])(f: C => Either[A, B]): ¬[C] =
    witness { c =>
      p.contradicts { case (notA, notB) =>
        f(c) match {
          case Left(a) => notA.contradicts(a)
          case Right(b) => notB.contradicts(b)
        }
      }
    }

  implicit def inhabited[A](implicit A: ¬[A]): ¬¬[¬[A]] = ¬¬.witness(f => f(A))

  implicit def uninhabited[A](implicit A: ¬¬[A]): ¬[¬[A]] = ¬.witness(nA => A.notUninhabited(nA))

  implicit def func[A, B](implicit A: ¬¬[A], B: ¬[B]): ¬[A => B] = ¬.witness(f => A.notUninhabited(B.contramap(f)))

  def proposition[A]: Proposition[¬[A]] =
    Proposition.witness((nnA: ¬¬[¬[A]]) => ¬.witness((a : A) => nnA.contradicts(A => A.contradicts(a))))

}
