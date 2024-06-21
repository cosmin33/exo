package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*

trait Exoadjunction[==>[_,_], -->[_,_], F[_], G[_]]:
  self =>

  val subL: Subcat[==>]
  val subR: Subcat[-->]
  def left : Exo[-->, ==>, F]
  def right: Exo[==>, -->, G]

  def iso[A, B]: (F[A] ==> B) <=> (A --> G[B])

  def unit  [A](using t: subL.TC[F[A]]): A --> G[F[A]] = iso[A, F[A]].to  (subL.id[F[A]])
  def counit[A](using t: subR.TC[G[A]]): F[G[A]] ==> A = iso[G[A], A].from(subR.id[G[A]])

  def flatmap  [A, B](r: A --> G[F[B]]): G[F[A]] --> G[F[B]] = (iso[A, F[B]].from andThen right.map[F[A], F[B]])(r)
  def coflatmap[A, B](r: F[G[A]] ==> B): F[G[A]] ==> F[G[B]] = (iso[G[A], B].to   andThen left.map[G[A], G[B]])(r)

  def subcatFG: Subcat.Aux[[a,b] =>> F[G[a]] ==> b, [a] =>> subR.TC[G[a]]] =
    new Subcat[[a,b] =>> F[G[a]] ==> b]:
      type TC[a] = subR.TC[G[a]]
      def id[A: TC]: F[G[A]] ==> A = counit[A]
      def andThen[A, B, C](ab: F[G[A]] ==> B, bc: F[G[B]] ==> C): F[G[A]] ==> C = subL.andThen(coflatmap(ab), bc)

  def subcatGF: Subcat.Aux[[a,b] =>> a --> G[F[b]], [a] =>> subL.TC[F[a]]] =
    new Subcat[[a,b] =>> a --> G[F[b]]]:
      type TC[a] = subL.TC[F[a]]
      def id[A: TC]: A --> G[F[A]] = unit[A]
      def andThen[A, B, C](ab: A --> G[F[B]], bc: B --> G[F[C]]): A --> G[F[C]] = subR.andThen(ab, flatmap(bc))

  def subcatFG_(using trans: [a] => subR.TC[a] => subR.TC[G[a]]): Subcat.Aux[[a, b] =>> F[G[a]] ==> b, subR.TC] =
    new Subcat[[a,b] =>> F[G[a]] ==> b]:
      type TC[a] = subR.TC[a]
      def id[A: TC]: F[G[A]] ==> A = counit[A](using trans[A](summon))
      def andThen[A, B, C](ab: F[G[A]] ==> B, bc: F[G[B]] ==> C): F[G[A]] ==> C = subL.andThen(coflatmap(ab), bc)

  def subcatGF_(using trans: [a] => subL.TC[a] => subL.TC[F[a]]): Subcat.Aux[[a, b] =>> a --> G[F[b]], subL.TC] =
    new Subcat[[a,b] =>> a --> G[F[b]]]:
      type TC[a] = subL.TC[a]
      def id[A: TC]: A --> G[F[A]] = unit[A](using trans[A](summon))
      def andThen[A, B, C](ab: A --> G[F[B]], bc: B --> G[F[C]]): A --> G[F[C]] = subR.andThen(ab, flatmap(bc))

object Exoadjunction:
  extension[->[_,_], F[_], G[_]](self: Exoadjunction[->, ->, F, G])
    def compose[P[_], Q[_]](that: Exoadjunction[->, ->, P, Q]): Exoadjunction[->, ->, [a] =>> P[F[a]], [a] =>> G[Q[a]]] =
      new Exoadjunction[->, ->, [a] =>> P[F[a]], [a] =>> G[Q[a]]]:
        val subL: Subcat[->] = self.subL
        val subR: Subcat[->] = self.subR
        def left:  Exo[->, ->, [a] =>> P[F[a]]] = self.left.compose(that.left)
        def right: Exo[->, ->, [a] =>> G[Q[a]]] = that.right.compose(self.right)
        def iso[A, B]: (P[F[A]] -> B) <=> (A -> G[Q[B]]) = that.iso[F[A], B] andThen self.iso[A, Q[B]]
