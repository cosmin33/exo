package io.cosmo.exo.categories.old

trait CocartesianOld

//trait Cocartesian[->[_, _], ⨁[_, _]] extends Monoidal[->, ⨁] with Symmetric[->, ⨁] {
//  def inl[A, B]: A -> ⨁[A, B]
//  def inr[A, B]: B -> ⨁[A, B]
//  def codiag[A]: ⨁[A, A] -> A
//  def |||[X, Y, Z](f: X ==> Z, g: Y ==> Z): ⨁[X, Y] -> Z
//}
//object Cocartesian {
//  trait Aux[->[_, _], TC0[_], ⨁[_, _], I]
//    extends Cocartesian[->, ⨁]
//      with Monoidal.Aux[Op[->,?,?], ⨁, TC0, I]
//      with Symmetric.Aux[Op[->,?,?], ⨁, TC0]
//}