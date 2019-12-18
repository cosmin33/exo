package io.cosmo.exo.categories

import io.cosmo.exo._
import io.cosmo.exo.categories.functors.{Endobifunctor, Exobifunctor}
import io.cosmo.exo.evidence._
import shapeless.the
import cats.implicits._

import scala.language.experimental.macros

trait Semicategory[->[_, _]] {
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C
}

object Semicategory
  extends SemicategoryImplicits
  with SubcategoryImplicits
  with DistributiveImplicits
  with CccImplicits {
  def apply[->[_,_]](implicit S: Semicategory[->]): Semicategory[->] = S
}
import SemicategoryHelpers._
trait SemicategoryImplicits extends SemicategoryImplicits01 {

  def function1OppCat: Subcat.AuxT[Opp[* => *]#l] = Subcat.oppCategory(function1)

  implicit def mapSemicategory: Semicategory[Map] = new Semicategory[Map] {
    override def andThen[A, B, C](ab: Map[A, B], bc: Map[B, C]): Map[A, C] =
      ab.flatMap {case (a, b) => bc.get(b).map(c => (a, c))}
  }

  implicit def liskovFnCategory: Subcat.AuxT[<~<] =
    new Subcat[<~<] {
      override type TC[a] = Trivial.T1[a]
      override def id[A](implicit A: Trivial.T1[A]): A <~< A = As.refl
      override def andThen[A, B, C](ab: A <~< B, bc: B <~< C): A <~< C = ab.andThen(bc)
    }

  implicit def function1: Ccc.Aux[Function1, Tuple2, Trivial.T1, Unit, Function1] =
      new Ccc[Function1] {
        type TC[a] = Trivial.T1[a]
        type Hom[a,b] = a => b
        type ⊙[a,b] = (a, b)
        type ProductId = Unit
        def cartesian = Associative.cartesianFn1Tuple
        def id[A](implicit A: TC[A]): A => A = identity
        def andThen[A, B, C](ab: A => B, bc: B => C): A => C = bc.compose(ab)
        def apply[A, B]: ⊙[A => B, A] => B = p => p._1(p._2)
        def curry[X, Y, Z](f: ⊙[X, Y] => Z): X => (Y => Z) = x => y => f((x, y))
        def uncurry[X, Y, Z](f: X => (Y => Z)): ⊙[X, Y] => Z = { case (x, y) => f(x)(y) }
      }

  implicit def leibnizGroupoid: Groupoid.AuxT[===] = new LeibnizGroupoidClass {}
}
trait SemicategoryImplicits01 extends SemicategoryImplicits02 {
  implicit def leibnizConcrete: Concrete.AuxT[===] = new LeibnizGroupoidClass {}
}
trait SemicategoryImplicits02 extends SemicategoryImplicits03
trait SemicategoryImplicits03


object SemicategoryHelpers {
  trait LeibnizGroupoidClass extends Groupoid.Proto[===, Trivial.T1] with Concrete.Proto[===, Trivial.T1] {
    override def id[A](implicit A: Trivial.T1[A]): A === A = Is.refl[A]
    override def andThen[A, B, C](ab: A === B, bc: B === C): A === C = bc.compose(ab)
    override def flip[A, B](ab: A === B): B === A = ab.flip
    override def concretize[A, B](ab: A === B): (A, Trivial.T1[A]) => (B, Trivial.T1[B]) =
      (a, p) => ab.subst[λ[X => (X, Trivial.T1[X])]]((a, p))
  }
  trait Fun1OppSubcategory[->[_,_], C[_]] extends Subcat[Opp[->]#l] {
    type TC[a] = C[a]
    protected def op: Subcat.Aux[->, C]
    override def id[A](implicit A: TC[A]): A -> A = op.id[A]
    override def andThen[X, Y, Z](ab: Y -> X, bc: Z -> Y): Z -> X = op.andThen(bc, ab)
  }
}

