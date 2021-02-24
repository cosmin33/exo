package io.cosmo.exo.categories

import cats.Inject
import cats.implicits._
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.evidence._
import io.cosmo.exo._
import shapeless.the

import scala.util.Either


trait Semicategory[->[_, _]] {
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C
}

object Semicategory extends SemicategoryImplicits {
  def apply[->[_,_]](implicit S: Semicategory[->]): Semicategory[->] = S

  def semicatToExobifunctor[->[_,_]](implicit s: Semicategory[->]): Exobifunctor[Dual[->,*,*], ->, * => *, ->] =
    new Exobifunctor[Dual[->,*,*], ->, * => *, ->] {
      def bimap[A, X, B, Y](left: Dual[->, A, X], right: B -> Y): (A -> B) => (X -> Y) = left.toFn >>>> _ >>>> right
    }
}

import io.cosmo.exo.categories.SemicategoryHelpers._
trait SemicategoryImplicits extends SemicategoryImplicits01 {
  implicit def mapSemicategory: Semicategory[Map] = new Semicategory[Map] {
    def andThen[A, B, C](ab: Map[A, B], bc: Map[B, C]): Map[A, C] =
      ab.flatMap {case (a, b) => bc.get(b).map(c => (a, c))}
  }
  implicit def liskov: Concrete.AuxT[<~<] = liskovClass
  implicit def function1: Ccc.Aux[* => *, Trivial.T1, (*, *), Unit, * => *] = function1Class

  implicit def leibnizGroupoid: Groupoid.AuxT[===] = leibnizClass
  implicit def injSubcat: Subcat.Aux[Inject, Trivial.T1] = injSubcatClass
}
trait SemicategoryImplicits01 extends SemicategoryImplicits02 {
  implicit def distFunc1: Distributive.Aux[* => *, Trivial.T1, (*, *), Unit, Either, Void] = function1Class
  implicit def distFunc2: Distributive.Aux[* => *, Trivial.T1, /\, Unit, \/, Void] =
    IsK2.lower2[Distributive.Aux[* => *, Trivial.T1, *[_,_], Unit, *[_,_], Void]].on(/\.leibniz, \/.leibniz)(function1Class)
  implicit def leibnizConcrete: Concrete.AuxT[===] = leibnizClass
  implicit def liskovTerminal: Terminal.Aux[<~<, Trivial.T1, Any] = liskovClass
}
trait SemicategoryImplicits02 extends SemicategoryImplicits03 {
  implicit def function1Terminal: Terminal.Aux[* => *, Trivial.T1, Unit] = function1Class
  implicit def liskovInitial: Initial.Aux[<~<, Trivial.T1, Void] = liskovClass
}
trait SemicategoryImplicits03 {
  implicit def function1Initial: Initial.Aux[* => *, Trivial.T1, Void] = function1Class
}

private[categories] object SemicategoryHelpers {
  val function1Class = new Function1Class {}
  val leibnizClass = new LeibnizGroupoidClass {}
  val liskovClass = new LiskovCatClass {}

  val injSubcatClass: Subcat.Aux[Inject, Trivial.T1] = new Subcat[Inject] {
    type TC[a] = Trivial.T1[a]
    def id[A](implicit A: TC[A]): Inject[A, A] = Inject[A, A]
    def andThen[A, B, C](ab: Inject[A, B], bc: Inject[B, C]): Inject[A, C] =
      new Inject[A, C] {
        val inj = ab.inj >>> bc.inj
        val prj = bc.prj(_).flatMap(ab.prj)
      }
  }

  trait LeibnizGroupoidClass extends Groupoid.Proto[===, Trivial.T1] with Concrete.Proto[===, Trivial.T1] {
    override def id[A](implicit A: Trivial.T1[A]): A === A = Is.refl[A]
    override def andThen[A, B, C](ab: A === B, bc: B === C): A === C = bc.compose(ab)
    override def flip[A, B](ab: A === B): B === A = ab.flip
    override def concretize[A, B](ab: A === B): (A, Trivial.T1[A]) => (B, Trivial.T1[B]) =
      (a, p) => ab.subst[λ[X => (X, Trivial.T1[X])]]((a, p))
  }

  trait LiskovCatClass
    extends Concrete[<~<]
      with Initial[<~<]
      with Terminal[<~<]
  {
    override type Initial = Void
    override type Terminal = Any
    override type TC[a] = Trivial.T1[a]
    def id[A](implicit A: Trivial.T1[A]): A <~< A = As.refl
    def andThen[A, B, C](ab: A <~< B, bc: B <~< C): A <~< C = ab.andThen(bc)
    def initialTC: T1[Void] = Trivial.trivialInstance
    def initiate[A](implicit A: T1[A]): Void <~< A = the[Void <~< A]
    def terminalTC: T1[Any] = Trivial.trivialInstance
    def terminate[A](implicit A: T1[A]): A <~< Any = the[A <~< Any]
    def concretize[A, B](f: A <~< B): (A, Trivial.T1[A]) => (B, Trivial.T1[B]) =
      { case (a, _) => (f(a), Trivial.trivialInstance) }
    override def toFunction[A: T1, B](f: A <~< B): A => B = a => f(a)
    override def concrete[A: T1, B](a: A)(f: A <~< B): B = f(a)
  }

  trait OppSubcategory[->[_,_], C[_]] extends Subcat[Opp[->]#l] {
    type TC[a] = C[a]
    protected def op: Subcat.Aux[->, C]
    override def id[A](implicit A: TC[A]): A -> A = op.id[A]
    override def andThen[X, Y, Z](ab: Y -> X, bc: Z -> Y): Z -> X = op.andThen(bc, ab)
  }

  trait OppSemicategory[->[_,_]] extends Semicategory[Opp[->]#l] {
    protected def op: Semicategory[->]
    override def andThen[X, Y, Z](ab: Y -> X, bc: Z -> Y): Z -> X = op.andThen(bc, ab)
  }

  trait Function1Class
    extends Terminal[* => *]
      with Initial[* => *]
      with Ccc[* => *]
      with Distributive[* => *, Tuple2, Either]
  {
    override type Terminal = Unit
    override type Initial = Void
    override type ProductId = Unit
    override type SumId = Void
    override type TC[a] = Trivial.T1[a]
    override type |->[a,b] = a => b
    override type ⊙[a,b] = (a, b)
    def cartesian = Associative.cartesianFn1Tuple
    def cocartesian = Associative.cocartesianFn1EitherDual
    def id[A](implicit A: TC[A]): A => A = identity
    def andThen[A, B, C](ab: A => B, bc: B => C): A => C = bc.compose(ab)
    override def apply[A, B](implicit t: TC[A |-> B]): ((A => B, A)) => B = { case (ab, a) => ab(a) }
    def curry[X, Y, Z](f: ((X, Y)) => Z): X => (Y => Z) = x => y => f((x, y))
    def uncurry[X, Y, Z](f: X => (Y => Z)): ⊙[X, Y] => Z = { case (x, y) => f(x)(y) }
    def terminalTC: Trivial.T1[Terminal] = Trivial.trivialInstance
    def terminate[A](implicit A: Trivial.T1[A]): A => Terminal = _ => ()
    def initialTC: Trivial.T1[Nothing] = Trivial.trivialInstance
    def initiate[A](implicit A: Trivial.T1[A]): Nothing => A = identity
    override def distribute[A: T1, B: T1, C: T1] = { case (a, bc) => bc.fold((a, _).asLeft, (a, _).asRight) }
  }




}

