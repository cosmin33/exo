package io.cosmo.exo


import scala.language.experimental.macros

package object evidence {

//  type ⋁[+A, +B] = Either[A, B]
//  type ⋀[+A, +B] = (A, B)

  type Proposition[A] = inhabitance.Proposition[A]
  val  Proposition = inhabitance.Proposition

  type Contractible[A] = inhabitance.Contractible[A]
  val  Contractible = inhabitance.Contractible

  type >~<[A, B] = Incomparable[A, B]

  type Uninhabited[/*-*/ A] = inhabitance.Uninhabited[A]
  val  Uninhabited = inhabitance.Uninhabited
  type ¬[A] = Uninhabited[A]
  val  ¬ = inhabitance.Uninhabited

  type Inhabited[A] = inhabitance.Inhabited[A]
  val  Inhabited = inhabitance.Inhabited
  type ¬¬[A] = Inhabited[A]
  val  ¬¬ = inhabitance.Inhabited

  type SingletonOf[A, +B] = inhabitance.SingletonOf[A, B]
  val  SingletonOf = inhabitance.SingletonOf
  type <::[A, +B] = inhabitance.SingletonOf[A, B]

  type ===[A, B]   = Is[A, B]

  type WeakApart[A, B] = weakapart.WeakApart[A, B]
  val  WeakApart = weakapart.WeakApart
  type =!=[A, B] = weakapart.WeakApart[A, B]
  val  =!= = weakapart.WeakApart

  //type =!!=[A[_], B[_]] = WeakApartK[A, B]

  type <~<[-A, +B] = As[A, B]
  val  <~< = As
  type >~>[+B, -A] = As[A, B]
  type </<[-A, +B] = StrictAs[A, B]

  type =~=[A[_], B[_]] = IsK[A, B]
  val  =~= = IsK
  type =~~=[A[_,_], B[_,_]] = IsK2[A, B]
  val =~~= = IsK2

  type =≈=[A[_[_]], B[_[_]]] = IsHK[A, B]
  val  =≈= = IsHK

  type TypeHolder[T] = TypeHolderModule.Aux[T]
  val  TypeHolder = TypeHolderModule
  type TypeHolder2[A, B] = TypeHolder2Module.Aux[A, B]
  val  TypeHolder2 = TypeHolder2Module
  type TypeHolder3[A, B, C] = TypeHolder3Module.Aux[A, B, C]
  val  TypeHolder3 = TypeHolder3Module
  type TypeHolderK[F[_]] = TypeHolderKModule.Aux[F]
  val  TypeHolderK = TypeHolderKModule
  type TypeHolderHK[H[_[_]]] = TypeholderHKModule.Aux[H]
  val  TypeHolderHK = TypeholderHKModule


}
