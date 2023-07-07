package io.cosmo.exo.inhabitance

import io.cosmo.exo.*

opaque type Inhabited[A] <: (A => Void) => Void = (A => Void) => Void

object Inhabited {
  def apply[A](using A: ¬¬[A]): ¬¬[A] = A
  def witness[A](f: (A => Void) => Void): ¬¬[A] = f
  def value[A](a: A): ¬¬[A] = witness[A](f => f(a))

  extension [A](inhabited: Inhabited[A])
    def contradicts(f: A => Void): Void = inhabited(f)
    def notUninhabited(f: ¬[A]): Void = contradicts(f.contradicts)
    def proved(using ev: Proposition[A]): A = ev.proved(using inhabited)
    def flatMap[B](f: A => ¬¬[B]): ¬¬[B] = witness(k => inhabited(a => f(a)(k)))
    def map[B](f: A => B): ¬¬[B] = flatMap(a => value(f(a)))

  given isoCanonic[A]: <=>[(A => Void) => Void, ¬¬[A]] = Iso.refl[¬¬[A]]

  def lemEither[A]: ¬¬[Either[A => Void, A]] = witness(k => k(Left(a => k(Right(a)))))

  def lemDisj[A]: ¬¬[(A => Void) \/ A] = witness(k => k(-\/(a => k(\/-(a)))))

  given singleton[A <: Singleton](using A: ValueOf[A]): ¬¬[A] =
    witness(f => f(A.value))

  given inhabited[A](using A: ¬¬[A]): ¬¬[¬¬[A]] =
    witness(f => f(A))

  given uninhabited[A](using na: ¬[A]): ¬[¬¬[A]] =
    ¬.witness(A => A.notUninhabited(na))

  given proposition[A]: Proposition[¬¬[A]] =
    Proposition.witness((p: ¬¬[¬¬[A]]) => p.flatMap(identity))

  given contractible[A](using A: ¬¬[A]): Contractible[¬¬[A]] =
    Contractible.witness[¬¬[A]](using inhabited, proposition[A])

  /** Law of excluded middle. */
  def lem[A]: ¬¬[¬[A] \/ A] = lemEither[A].map(e => \/(e.left.map(¬.witness[A])))

  def and[A, B](f: (A, B) => Void): ¬¬[(A => Void) \/ (B => Void)] =
    witness(p => p(\/-(b => p(-\/(a => f(a, b))))))

  def imp[A, B](f: A => B): ¬¬[(A => Void) \/ B] = witness(k => k(-\/(a => k(\/-(f(a))))))

  def andE[A, B](f: (A, B) => Void): ¬¬[Either[A => Void, B => Void]] =
    witness(p => p(Right(b => p(Left(a => f(a, b))))))

  def impE[A, B](f: A => B): ¬¬[Either[A => Void, B]] =
    witness(k => k(Left(a => k(Right(f(a))))))

  def pierce[A]: ¬¬[((A => Void) => A) => A] =
    witness(k => k((p: (A => Void) => A) => p((a: A) => k(_ => a))))

}
