package io.cosmo.exo

import io.cosmo.exo.evidence.{<~<, IsInjective}
import io.cosmo.exo.evidence.variance._
import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite

class InstanceOfTests extends AnyFunSuite with Matchers {

//  implicitly[IsCovariant[InstanceOf]]
//  implicitly[IsInjective[InstanceOf]]
//  implicitly[StrictlyCovariant[InstanceOf]]


  locally {

    def sub[B <: A, A](): Unit = ()

    sub[Any {type TC[_]}, Any]()
    sub[Nothing, Nothing {type TC[_]}]()

    //def jj[x] = implicitly[InstOfSub[Any {type TC[_]}, x] <~< InstOf[x]]

    //def ss[x] = sub[InstOfSub[Any {type TC[_]}, x], InstOf[x]]()

  }


}
