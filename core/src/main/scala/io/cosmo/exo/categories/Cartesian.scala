package io.cosmo.exo.categories

import io.cosmo.exo._

trait Cartesian[->[_, _], ⨂[_, _]] extends Monoidal[->, ⨂] with Symmetric[->, ⨂] {
  def fst[A, B]: ⨂[A, B] -> A
  def snd[A, B]: ⨂[A, B] -> B
  def diag[A]: A -> ⨂[A, A]
  def &&&[X, Y, Z](f: X -> Y, g: X -> Z): X -> ⨂[Y, Z]

  def pair[A, B, X, Y](f: A -> B, g: X -> Y): ⨂[A, X] -> ⨂[B, Y] =
    &&&(C.andThen(fst[A, X], f), C.andThen(snd[A, X], g))

  def isoCartesian[X, Y, Z]: (X -> Y, X -> Z) <=> (X -> ⨂[Y, Z]) =
    Iso.unsafeT(p => &&&(p._1, p._2), fn => (C.andThen(fn, fst[Y, Z]), C.andThen(fn, snd[Y, Z])))

}

object Cartesian extends CartesianInstances with CartesianSyntax {
  type Aux[->[_, _], ⨂[_, _], TC0[_], I] = Cartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }

  trait Proto[->[_, _], ⨂[_, _], TC0[_], I] extends Cartesian[->, ⨂] { type TC[a] = TC0[a]; type Id = I }

}

trait CartesianSyntax {
  implicit def cartesianOps[->[_, _], ⨂[_, _], C[_], I](
    source: Cartesian.Aux[->, ⨂, C, I]
  ): CartesianOps[->, ⨂, C, I] = new CartesianOps(source)

  class CartesianOps[->[_, _], ⨂[_, _], C[_], I](c: Cartesian.Aux[->, ⨂, C, I]) {

  }

  implicit def coCartesianOps[->[_, _], ⨂[_, _], C[_], I](
    source: Cartesian.Aux[λ[(a, b) => b -> a], ⨂, C, I]
  ): CocartesianOps[->, ⨂, C, I] = new CocartesianOps(source)

  class CocartesianOps[->[_, _], ⨁[_, _], C[_], I](c: Cartesian.Aux[λ[(a, b) => b -> a], ⨁, C, I]) {
    object opp {
      def inl[A, B]: A -> ⨁[A, B] = c.fst
      def inr[A, B]: B -> ⨁[A, B] = c.snd
      def codiag[A]: ⨁[A, A] -> A = c.diag
      def |||[X, Y, Z](f: X -> Z, g: Y -> Z): ⨁[X, Y] -> Z = c.&&&(f,g)
    }
  }
}

trait CartesianInstances {
}

trait HCartesian[->[_,_], HList, ::[_, _] <: HList, Nil <: HList] extends HMonoidal[->, HList, ::, Nil] {
  def head[H, T <: HList]: (H :: T) -> H
  def tail[H, T <: HList]: (H :: T) -> T
  def diag[A]: A -> (A :: Nil) = coid[A]
  def &&&[X, H, T <: HList](f: X -> H, g: X -> T): X -> (H :: T)
}

//trait CartesianK[->[_[_],_[_]], ⨂[_[_],_[_],_]] extends MonoidalK[->, ⨂] with SymmetricK[->, ⨂] {
//  def fst[F[_], G[_]]: ⨂[F, G, *] -> F
//  def snd[F[_], G[_]]: ⨂[F, G, *] -> G
//  def diag[F[_], G[_]]: F -> ⨂[F, F, *]
//  def &&&[X[_], Y[_], Z[_]](f: X -> Y, g: X -> Z): X -> ⨂[Y, Z, *]
//}
//object CartesianK {
//  trait Aux[->[_[_],_[_]], TC0[_[_]], ⨂[_[_],_[_],_], I[_]]
//    extends CartesianK[->, ⨂]
//      with MonoidalK.Aux[->, ⨂, TC0, I]
//      with SymmetricK.Aux[->, ⨂, TC0]
//}

