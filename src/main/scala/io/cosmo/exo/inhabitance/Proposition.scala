package io.cosmo.exo.inhabitance

import io.cosmo.exo.*

trait Proposition[A] extends WeakProposition[A] {
  A =>
  def proved(using A: ¬¬[A]): A

  def isomap[B](f: A <=> B): Proposition[B] = new Proposition[B]:
    def proved(using p: ¬¬[B]): B = f.to(A.proved(using p.map(f.from)))

  def zip[B](using B: Proposition[B]): Proposition[(A, B)] = new Proposition[(A, B)]:
    def proved(using p: ¬¬[(A, B)]): (A, B) = (A.proved(using p.map(_._1)), B.proved(using p.map(_._2)))
}

object Proposition {
  def apply[A](using A: Proposition[A]): Proposition[A] = A

  def witness[A](fn: ¬¬[A] => A): Proposition[A] = new Proposition[A]:
    def proved(using p: ¬¬[A]): A = fn(p)

  // This covers the initial object.
  given voidIsProposition: Proposition[Void] = new Proposition[Void]:
    def proved(using p: ¬¬[Void]): Void = p(a => a)

  // This covers Unit & other terminal objects.
  given unitProp: Proposition[Unit] = new Proposition[Unit]:
    def proved(using p: ¬¬[Unit]): Unit = ()

  given singleton[A <: Singleton](using A: ValueOf[A]): Proposition[A] = new Proposition[A]:
    def proved(using p: ¬¬[A]): A = A.value

  given negation[A]: Proposition[¬[A]] = negationV[A].isomap(Uninhabited.isoCanonic[A])

  def negationV[A]: Proposition[A => Void] = new Proposition[A => Void]:
    def proved(using p: ¬¬[A => Void]): A => Void = (a: A) => p((k: A => Void) => k(a))

  // Proposition is proposition
  given propOfProp[A](using prop: Proposition[A]): Proposition[Proposition[A]] = new Proposition[Proposition[A]]:
    def proved(using p: ¬¬[Proposition[A]]): Proposition[A] = prop

}
