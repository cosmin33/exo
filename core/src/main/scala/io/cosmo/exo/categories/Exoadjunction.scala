package io.cosmo.exo.categories

import io.cosmo.exo.categories.functors.Exo
import io.cosmo.exo.{<=>, Iso, ∀}

trait Exoadjunction[==>[_,_], -->[_,_], F[_], G[_]] { self =>
  val subL: Subcat[==>]
  val subR: Subcat[-->]
  def F: Exo[-->, ==>, F]
  def G: Exo[==>, -->, G]

  def iso[A, B]: (F[A] ==> B) <=> (A --> G[B]) =
    Iso.unsafe(fab => subR.andThen(unit[A], G.map(fab)), agb => subL.andThen(F.map(agb), counit[B]))

  def unit  [A]: A --> G[F[A]] // = iso[A, F[A]].to  (subL.id[F[A]])
  def counit[A]: F[G[A]] ==> A // = iso[G[A], A].from(subR.id[G[A]])

  def unitK  : ∀[λ[a => a --> G[F[a]]]] = ∀.of[λ[a => a --> G[F[a]]]].from(unit)
  def counitK: ∀[λ[a => F[G[a]] ==> a]] = ∀.of[λ[a => F[G[a]] ==> a]].from(counit)

  def monad  [A, B](r: A --> G[F[B]]): G[F[A]] --> G[F[B]] = (iso[A, F[B]].from andThen G.map[F[A], F[B]])(r)
  def comonad[A, B](r: F[G[A]] ==> B): F[G[A]] ==> F[G[B]] = (iso[G[A], B].to   andThen F.map[G[A], G[B]])(r)

  def subcatFG: Subcat.Aux[λ[(a,b) => F[G[a]] ==> b], λ[a => subR.TC[G[a]]]] =
    new Subcat[λ[(a,b) => F[G[a]] ==> b]] {
      type TC[a] = subR.TC[G[a]]
      def id[A: TC]: F[G[A]] ==> A = counit[A]
      def andThen[A, B, C](ab: F[G[A]] ==> B, bc: F[G[B]] ==> C): F[G[A]] ==> C = subL.andThen(comonad(ab), bc)
    }

  def subcatGF: Subcat.Aux[λ[(a,b) => a --> G[F[b]]], λ[a => subL.TC[F[a]]]] =
    new Subcat[λ[(a,b) => a --> G[F[b]]]] {
      type TC[a] = subL.TC[F[a]]
      def id[A: TC]: A --> G[F[A]] = unit[A]
      def andThen[A, B, C](ab: A --> G[F[B]], bc: B --> G[F[C]]): A --> G[F[C]] = subR.andThen(ab, monad(bc))
    }

  def subcatFG_ : Subcat.Aux[λ[(a,b) => F[G[a]] ==> b], subR.TC] =
    new Subcat[λ[(a,b) => F[G[a]] ==> b]] {
      type TC[a] = subR.TC[a]
      def id[A: TC]: F[G[A]] ==> A = counit[A]
      def andThen[A, B, C](ab: F[G[A]] ==> B, bc: F[G[B]] ==> C): F[G[A]] ==> C = subL.andThen(comonad(ab), bc)
    }
  def subcatGF_ : Subcat.Aux[λ[(a,b) => a --> G[F[b]]], subL.TC] =
    new Subcat[λ[(a,b) => a --> G[F[b]]]] {
      type TC[a] = subL.TC[a]
      def id[A: TC]: A --> G[F[A]] = unit[A]
      def andThen[A, B, C](ab: A --> G[F[B]], bc: B --> G[F[C]]): A --> G[F[C]] = subR.andThen(ab, monad(bc))
    }

}

object Exoadjunction {

  class EndoAdjunctionOps[->[_,_], F[_], G[_]](self: Exoadjunction[->, ->, F, G]) {
    def compose[P[_], Q[_]](that: Exoadjunction[->, ->, P, Q]): Exoadjunction[->, ->, λ[a => P[F[a]]], λ[a => G[Q[a]]]] =
      new Exoadjunction[->, ->, λ[a => P[F[a]]], λ[a => G[Q[a]]]] {
        val subL: Subcat[->] = self.subL
        val subR: Subcat[->] = self.subR
        def F: Exo[->, ->, λ[a => P[F[a]]]] = that.F.compose(self.F)
        def G: Exo[->, ->, λ[a => G[Q[a]]]] = self.G.compose(that.G)
        def unit  [A]: A -> G[Q[P[F[A]]]] = subL.andThen(self.unit[A], self.G.map(that.unit[F[A]]))
        def counit[A]: P[F[G[Q[A]]]] -> A = subR.andThen(that.F.map(self.counit[Q[A]]), that.counit[A])
      }
  }

}