package io.cosmo.exo.categories.play.deptypes

import org.scalatest.funsuite.AnyFunSuite
import shapeless.Refute

class DepTypeTests extends AnyFunSuite {


  locally {
    type Rep[A <: Bool] = A#If[ Int, Long, AnyVal ]
    implicitly[ Rep[True] =:= Int ]
    implicitly[ Refute[Rep[False] =:= Int ]]
    implicitly[ Rep[False] =:= Long ]

    import Bool._

    implicitly[ True && False || Not[False] =:= True ]
  }

  test("blah") {
    import Bool._
    def toBoolean[B <: Bool](implicit b: BoolRep[B]): Boolean = b.value

    assert(toBoolean[True && False || Not[False]])

  }

  locally {
    import Nat._

    type C = _0#FoldR[ Int, AnyVal, Fold[Nat, AnyVal]]
    // compiles, because C is Int
    implicitly[ C =:= Int ]
    // doesn't compile, because C is not AnyVal
    //implicitly[ C =:= AnyVal ]

  }

  def list(n: Int) = (n to 1 by -1).toList


  test("dense stuff") {
    import Dense._
    toInt[ _14 ] == 14
    toInt[ _5#Inc ] == 6
    toInt[ _5#Add[_7] ] == 12
    toInt[ _12#Mult[_8]#Mult[_13] ] == 1248
    toInt[ _4#Exp[_15] ] == 1073741824
  }

}
