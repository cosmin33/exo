package io.cosmo.exo.categories

import cats.Inject
import cats.implicits._
import io.cosmo
import io.cosmo.exo
import io.cosmo.exo.{~>, _}
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.Exofunctor.{Con, Cov}
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.evidence._
import io.cosmo.exo.typeclasses.{IsTypeF, TypeF}
import shapeless.the

import scala.util.Either


trait Semicategory[->[_, _]] {
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C
}

private trait SemicategoryIsProfunctor[->[_, _]] extends Exobifunctor[Dual[->,*,*], ->, * => *, ->] {
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
  def bimap[A, X, B, Y](left: Dual[->, A, X], right:  B -> Y): A -> B => X -> Y = ab => andThen(left, andThen(ab, right))
  def leftMap[A, B, Z](fn: Dual[->, A, Z]): A -> B => Z -> B = andThen(fn.toFn, _)
  def rightMap[A, B, Z](fn: B -> Z): A -> B => A -> Z = andThen(_, fn)
}

object Semicategory extends SemicategoryImplicits {
  def apply[->[_,_]](implicit S: Semicategory[->]): Semicategory[->] = S
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
    override def toFunction[A, B](f: A <~< B)(implicit eq: =~=[T1, T1]) = f.apply
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
      with Distributive[* => *]
  {
    override type Terminal = Unit
    override type Initial = Void
    override type ⨂[a, b] = (a, b)
    override type ProductId = Unit
    override type ⨁[a, b] = Either[a, b]
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
    def distribute[A: TC, B: TC, C: TC]: A ⨂ (B ⨁ C) => A ⨂ B ⨁ (A ⨂ C) =
      { case (a, bc) => bc.fold((a, _).asLeft, (a, _).asRight) }
  }

  trait FunKCartesian extends Cartesian[FunK, Tuple2] {
    override type Id = TypeF[UnitK]
    override type TC[a] = IsTypeF[a]
    override def C: Subcat.Aux[FunK, IsTypeF] = FunK.categ
    override def bifunctor: Endobifunctor[FunK, Tuple2] = ???

    private def fst1[F[_], G[_]]: λ[x => (F[x], G[x])] ~> F = ∀.mk[λ[x => (F[x], G[x])] ~> F].from(p => p._1)
    override def fst[A: TC, B: TC]: FunK[(A, B), A] = {
      val tca: IsTypeF[A] = implicitly[TC[A]]
      val tcb: IsTypeF[B] = implicitly[TC[B]]
      type F[x] = tca.Type[x]
      type G[x] = tcb.Type[x]
      val f1: λ[x => (F[x], G[x])] ~> F = fst1[F, G]
      val r1: FunK[TypeF[λ[x => (F[x], G[x])]], TypeF[F]] = FunK(f1)
      val r0: FunK[(TypeF[F], TypeF[G]), TypeF[λ[x => (F[x], G[x])]]] = ???
      // r0 >>> r1 // the result

      ???
    }

    override def snd[A: TC, B: TC]: FunK[(A, B), B] = ???
    override def diag[A: TC]: FunK[A, (A, A)] = ???
    override def &&&[X, Y, Z](f: FunK[X, Y], g: FunK[X, Z]): FunK[X, (Y, Z)] = ???
    override def braid[A: TC, B: TC]: FunK[(A, B), (B, A)] = ???
    override def idl  [A: TC]: FunK[(TypeF[UnitK], A), A] = ???
    override def coidl[A: TC]: FunK[A, (TypeF[UnitK], A)] = ???
    override def idr  [A: TC]: FunK[(A, TypeF[UnitK]), A] = ???
    override def coidr[A: TC]: FunK[A, (A, TypeF[UnitK])] = ???
    override def associate  [X: TC, Y: TC, Z: TC]: FunK[((X, Y), Z), (X, (Y, Z))] = ???
    override def diassociate[X: TC, Y: TC, Z: TC]: FunK[(X, (Y, Z)), ((X, Y), Z)] = ???
  }

  trait FunKClass
    extends Terminal[FunK]
    with Initial[FunK]
    //with Ccc[FunK]
    with Distributive[FunK]
  {
    override type Terminal = TypeF[UnitK]
    override type Initial = TypeF[VoidK]
    override type ⨂[a, b] = (a, b)
    override type ProductId = TypeF[UnitK]
    override type ⨁[a, b] = Either[a, b]
    override type SumId = TypeF[VoidK]
    override type TC[a] = IsTypeF[a]
    def terminalTC = IsTypeF[UnitK]
    def terminate[A](implicit A: IsTypeF[A]): FunK[A, TypeF[UnitK]] = {
      val ff: A.Type ~> UnitK = ∀.mk[A.Type ~> UnitK].from(_ => ())
      A.is.subst[FunK[*, TypeF[UnitK]]](FunK[A.Type, UnitK](ff))
    }
    def initialTC = IsTypeF[VoidK]
    def initiate[A](implicit A: IsTypeF[A]): FunK[TypeF[VoidK], A] = {
      val ff: VoidK ~> A.Type = ∀.mk[VoidK ~> A.Type].from(identity)
      A.is.subst[FunK[TypeF[VoidK], *]](FunK[VoidK, A.Type](ff))
    }
    def id[A](implicit A: TC[A]): FunK[A, A] =
      Is.lift2[FunK](A.is, A.is)(FunK(∀.mk[A.Type ~> A.Type].from(a => a)))
    def andThen[A, B, C](ab: FunK[A, B], bc: FunK[B, C])  = new FunK[A, C] {
      type TypeA[x] = ab.TypeA[x]
      type TypeB[x] = bc.TypeB[x]
      val (eqA, eqB) = (ab.eqA, bc.eqB)
      val instance = ∀.mk[ab.TypeA ~> bc.TypeB].from(
        TypeF.injectivity(ab.eqB.andThen(bc.eqA.flip))
          .subst(ab.instance).apply
          .andThen(bc.instance.apply))
    }

    def cartesian: Cartesian.Aux[FunK, Tuple2, IsTypeF, TypeF[UnitK]] = ???
    def cocartesian: Cartesian.Aux[Dual[FunK,*,*], Either, IsTypeF, TypeF[VoidK]] = ???

    def distribute[A: TC, B: TC, C: TC]: FunK[(A, Either[B, C]), Either[(A, B), (A, C)]] = {
      val tca: IsTypeF[A] = implicitly[TC[A]]
      val tcb: IsTypeF[B] = implicitly[TC[B]]
      val tcc: IsTypeF[C] = implicitly[TC[C]]
      type F[x] = tca.Type[x]
      type G[x] = tcb.Type[x]
      type H[x] = tcc.Type[x]
      val dd: λ[a => (F[a], Either[G[a], H[a]])] ~> λ[a => Either[(F[a], G[a]), (F[a], H[a])]] = distribute1[F, G, H]
      val rr: FunK[TypeF[λ[a => (F[a], Either[G[a], H[a]])]], TypeF[λ[a => Either[(F[a], G[a]), (F[a], H[a])]]]] = FunK(dd)
      ???
    }

    def distribute1[F[_], G[_], H[_]]: λ[a => (F[a], Either[G[a], H[a]])] ~> λ[a => Either[(F[a], G[a]), (F[a], H[a])]] =
      ∀.mk[λ[a => (F[a], Either[G[a], H[a]])] ~> λ[a => Either[(F[a], G[a]), (F[a], H[a])]]].from({
        case (f, ei) => ei.bimap(g => (f, g), h => (f, h))
      })


  }


}

