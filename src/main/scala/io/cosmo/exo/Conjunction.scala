package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.Unsafe

opaque type Conjunction[L, R] >: (L, R) = (L, R)

type /\[A, B] = Conjunction[A, B]
val /\ = Conjunction

object Conjunction {
  def apply[L, R](l: L, r: R): /\[L, R] = (l, r)

  def unfold [A, B, X](x: X)(f1: X => A, f2: X => B): A /\ B = (f1(x), f2(x))
  def unfold3[A, B, C, X](x: X)(f1: X => A, f2: X => B, f3: X => C): /\[A, /\[B, C]] = (f1(x), (f2(x), f3(x)))
  def unfold4[A, B, C, D, X](x: X)(f1: X => A, f2: X => B, f3: X => C, f4: X => D): /\[A, /\[B, /\[C, D]]] = (f1(x), (f2(x), (f3(x), f4(x))))
  def unfold5[A, B, C, D, E, X](x: X)(f1: X => A, f2: X => B, f3: X => C, f4: X => D, f5: X => E): /\[A, /\[B, /\[C, /\[D, E]]]] = (f1(x), (f2(x), (f3(x), (f4(x), f5(x)))))

  def both[A, B, C](ab: A => B, ac: A => C): A => (B /\ C) = a => (ab(a), ac(a))

  def unsafeLeibniz: Tuple2 =~~= /\ = =~~=.refl

  given iso[A, B]: ((A, B) <=> (A /\ B)) = Iso.refl

//  given isoK2: (Tuple2 <~~> /\) = /\.unsafeLeibniz.toIso
  
  given bifunctor: Endobifunctor[Function, /\] with
    def bimap[A, B, C, D](ab: A => B, cd: C => D): (A /\ C) => (B /\ D) = p => (ab(p._1), cd(p._2))

  given productTypeclass[T[_], A, B](using L: LaxSemigroupal[/\, Function, /\, T], ta: T[A], tb: T[B]): T[A /\ B] =
    L.product(/\(ta, tb))

  given [A, B](using a: A, b: B): (A /\ B) = (a, b)

  extension[A, B] (p: Conjunction[A, B])
    def tuple: (A, B) = p
    def _1: A = p._1
    def _2: B = p._2
    def swap: Conjunction[B, A] = (p._2, p._1)

}

