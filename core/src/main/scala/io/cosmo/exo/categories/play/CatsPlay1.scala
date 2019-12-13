package io.cosmo.exo.categories.play

import io.cosmo.exo.evidence._

object CatsPlay1 {

  class Matrix[n: * <:: Int, m: * <:: Int]

  def read(path: String): Matrix[_, _] = ???

  val m1: Matrix[_,_] = ???
  val m2: Matrix[_,_] = ???

//  (m1.m compare m2.n) match {
//    case Right(p: m1.m.type === m2.n.type) => ???
//    case Left(p) => ???
//  }

}
