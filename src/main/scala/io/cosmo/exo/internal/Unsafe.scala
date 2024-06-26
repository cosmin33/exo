package io.cosmo.exo.internal

import io.cosmo.exo.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.inhabitance.*

object Unsafe {
  @inline def not[A]: A => Void = _ => sys.error("unexpected")

  @inline def is[A, B]: A === B = Is.refl[A].asInstanceOf[A === B]

  @inline def weakApart[A, B]: A =!= B = WeakApart.witness(not[A === B])

//  @inline def apart[A, B](A: TypeId[A], B: TypeId[B]): Apart[A, B] = Apart.witness(weakApart[A, B], A, B)

  @inline def isK[A[_], B[_]]: A =~= B = IsK.refl[A].asInstanceOf[A =~= B]
  
  @inline def isHK[A[_[_]], B[_[_]]]: A =≈= B = IsHK.refl[A].asInstanceOf[A =≈= B]

  @inline def isK2[A[_,_], B[_,_]]: A =~~= B = IsK2.refl[A].asInstanceOf[A =~~= B]

  @inline def as[A, B]: A <~< B = As.refl[A].asInstanceOf[A <~< B]

//  @inline def strictAs[A, B]: A </< B = StrictAs.bottomTop.asInstanceOf[A </< B]
//
  @inline def incomparable[A, B]: A >~< B = Incomparable.witness(¬.witness(not[A <~< B]), ¬.witness(not[B <~< A]))
}
