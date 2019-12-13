package io.cosmo.exo.categories.play

import cats.Order

import scala.collection.immutable.SortedSet

object DeptypesExperiment {

  trait SetSig {
    type F[_]
    type Cons[_]
    def empty[A: Cons]: F[A]
    def singleton[A: Cons](a: A): F[A]
    def union[A: Cons](a: F[A], b: F[A]): F[A]
    def diff[A: Cons](a: F[A], b: F[A]): F[A]

//    // Use your imagination from this point on
//    def assoc[A : C](a: F[A], b: F[A], c: F[A]): union(union(a, b), c) =
//    union(a, union(b, c))
//    def commute[A : C](a: F[A], b: F[A]): union(a, b) =
//    union(b, a)
//    // ...
  }

  object RBTree extends SetSig {
    type F[a] = SortedSet[a]
    type Cons[a] = Ordering[a]
    def empty[A: Cons] = SortedSet.empty[A]
    def singleton[A: Cons](a: A) = SortedSet.apply(a)
    def union[A: Cons](a: F[A], b: F[A]) = a ++ b
    def diff[A: Cons](a: F[A], b: F[A]) = a -- b
  }
  type RBTree[A] = RBTree.F[A]

  // Recursor
  def rec[A, Z](fa: RBTree[A])(
    empty: Order[A] => Z,
    singleton: Order[A] => A => Z,
    union: Order[A] => (Z, Z) => Z,
    diff: Order[A] => (Z, Z) => Z,
  ): Z = ???

  import RBTree._
//  def ind[A, Z[fa : RBTree[A]]](a: RBTree[A])(
//    emptyʹ: Z[empty[A]],
//    singletonʹ: (a: A) => Z[singleton(a)],
//    unionʹ: C[A] => (a: F[A], b: F[A]) => (Z[a], Z[b]) => Z[union(a, b)],
//  ): C[a]

}
