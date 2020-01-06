package io.cosmo.exo.forall

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import io.cosmo.exo._

class ForallTests extends AnyFunSuite with Matchers {

  test("blah") {

    val φ: List ~> Option = ∀.mk[List ~> Option].from(_.headOption)
    val l = List(1, 2)
    val rc = φ.apply[Int].apply(l)
    val rh = φ.exec(l)
    val rb = φ.apply(l)
    val ra = φ[Int](l)

  }

  test("forallstuff") {

    import cats.Semigroup

    object ForallUsage {

      def listSemigroup[A]: Semigroup[List[A]] = (x: List[A], y: List[A]) => x ++ y

      // isntances can be created using `of` syntax
      val nil: ∀[List] = ∀.of[List].from(Nil)
      val emptyMap: ∀∀[Map] = ∀∀.of[Map].from(Map())

      // or `mk` syntax
      val nil1: ∀[List] = ∀.mk[∀[List]].from(Nil)
      val emptyMap1: ∀∀[Map] = ∀∀.mk[∀∀[Map]].from(Map())


      /* universally quantified semigroup */

      type Plus[F[_]] = ∀[λ[A => Semigroup[F[A]]]]

      // create an instance
      val listPlus: Plus[List] = ∀.mk[Plus[List]].from(listSemigroup)

      // use the instance
      assert( listPlus[Int].combine(List(1, 2), List(3, 4)) == List(1, 2, 3, 4) )

      /* natural transformation */

      // create an instance
      val headOption: List ~> Option = ∀.mk[List ~> Option].from(_.headOption)

      // use the instance
      assert( headOption[Int](List(1, 2, 3)) == Some(1) )

      // extra syntax for applying a natural transformation to universally quantified value
      implicit class NaturalTransformationOps[F[_], G[_]](trans: F ~> G) {
        def $(f: ∀[F]): ∀[G] = ∀.of[G](trans.exec(f.apply))
      }

      // applying a universally quantified function to a universally quantified value
      // yields a universally quantified value
      val none: ∀[Option] = headOption $ nil

      // create an instance
      type Option2[A, B] = Option[(A, B)]
      val pick: Map ~~> Option2 = ∀∀.mk[Map ~~> Option2].from(_.headOption)

      // use the instance
      assert( pick[String, Int](Map("hi" -> 5)) == Some("hi" -> 5) )

      // applying a universally quantified function to a universally quantified value
      // yields a universally quantified value
//      val none2: ∀∀[Option2] = pick $ emptyMap
    }
  }

}
