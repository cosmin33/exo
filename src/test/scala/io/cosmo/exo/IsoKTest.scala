package io.cosmo.exo

import zio.test._

//object IsoKTest extends ZIOSpecDefault {
//
//  def isoReverse1: List <~> List = ∀.mk[List <~> List].from(Iso.unsafe(_.reverse, _.reverse))
//  def isoReverse2: List <~> List = <~>.unsafe[List, List]([A] => (l: List[A]) => l.reverse, [A] => (l: List[A]) => l.reverse)
//  def isoReverse3: List <~> List = <~>.unsafe[List, List]([a] => () => Iso.unsafe(_.reverse, _.reverse))
//  def isoReverse4: List <~> List = <~>.unsafe[List, List](
//    ~>[List, List]([a] => (l: List[a]) => l.reverse),
//    ~>[List, List]([a] => (l: List[a]) => l.reverse)
//  )
//
//  def id: List <~> List = isoReverse1 andThen isoReverse2
//
//  def spec = suite("~>")(
//    test("run correctly") {
//      assertTrue(isoReverse1[Int].to(List(1,2,3)) == List(3,2,1)) &&
//        assertTrue(isoReverse1[Int].from(List(1,2,3)) == List(3,2,1)) &&
//        assertTrue(isoReverse1[Int].to(List(1,2,3)) == isoReverse2[Int].to(List(1,2,3))) &&
//        assertTrue(id[Int].to(List(1, 2, 3)) == List(1, 2, 3))
//    }
//  )
//}
