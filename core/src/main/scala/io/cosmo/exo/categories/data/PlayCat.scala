package io.cosmo.exo.categories.data

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories.Trivial.trivialInstance
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors.{Endobifunctor, Exobifunctor, Exofunctor, LaxSemigroupal, OplaxSemigroupal}

case class PlayCat[F[_], A, B](fn: F[A] => F[B])

object PlayCat extends PlayCatImplicits {
}

case class PlayCat1[->[_,_], F[_], A, B](fn: F[A] -> F[B])
object PlayCat1 extends PlayCat1Implicits {

}

trait PlayCat1Implicits extends PlayCat1Implicits01 {
  import PlayCat1Helpers._
  implicit def subcat[->[_,_], T[_], F[_]](implicit
    S: Subcat.Aux[->, T], FT: T ~> λ[a => T[F[a]]]
  ): Subcat.Aux[PlayCat1[->, F,*,*], T] = new SubcatPlayCat[->, T, F] { val sub = S; val ft = FT }

  implicit def bifunctorProd[==>[_,_], -->[_,_], ~~>[_,_], ⊙[_,_], T[_], F[_]](implicit
    S: Semicategory[~~>],
    LS: LaxSemigroupal[⊙, ~~>, ⊙, F],   //   LaxSemigroupal[Any2, /\, ~~>, /\, F] //would suffice
    OS: OplaxSemigroupal[⊙, ~~>, ⊙, F], // OplaxSemigroupal[Any2, /\, ~~>, /\, F] //would suffice
    F: Exobifunctor[==>, -->, ~~>, ⊙]
  ): Exobifunctor[PlayCat1[==>, F,*,*], PlayCat1[-->, F,*,*], PlayCat1[~~>, F,*,*], ⊙] =
    new Exobifunctor[PlayCat1[==>, F,*,*], PlayCat1[-->, F,*,*], PlayCat1[~~>, F,*,*], ⊙] {
      def bimap[A, X, B, Y](left: PlayCat1[==>, F, A, X], right: PlayCat1[-->, F, B, Y]): PlayCat1[~~>, F, A ⊙ B, X ⊙ Y] =
        PlayCat1(OS.opProduct[A, B] >>>> F.bimap(left.fn, right.fn) >>>> LS.product[X, Y])
    }



}
trait PlayCat1Implicits01 extends PlayCat1Implicits02 {

}
trait PlayCat1Implicits02 {

}

object PlayCat1Helpers {
  trait SubcatPlayCat[->[_,_], T[_], F[_]] extends Subcat[PlayCat1[->, F, *, *]] {
    protected def sub: Subcat.Aux[->, T]
    protected def ft: T ~> λ[a => T[F[a]]]
    type TC[a] = T[a]
    def id[A](implicit ta: T[A]): PlayCat1[->, F, A, A] = PlayCat1(sub.id[F[A]](ft.apply[A](ta)))
    def andThen[A, B, C](ab: PlayCat1[->, F, A, B], bc: PlayCat1[->, F, B, C]): PlayCat1[->, F, A, C] = PlayCat1(sub.andThen(ab.fn, bc.fn))
  }

  trait AssocPlayCatConj[->[_,_], ⨂[_,_], T[_], F[_]] extends Associative[PlayCat1[->,F,*,*], ⨂] {
    type TC[a] = T[a]
    protected def F: Endofunctor[->, F]
    protected def P: Associative.Aux[->, ⨂, T]
    implicit protected def sub: Subcat.Aux[->, T]
    implicit protected def ft: T ~> λ[a => T[F[a]]]
    def C: Subcat.Aux[PlayCat1[->, F,*,*], TC] = implicitly
    def associate  [X: TC, Y: TC, Z: TC]: PlayCat1[->, F, X ⨂ Y ⨂ Z, X ⨂ (Y ⨂ Z)] =
      PlayCat1(F.map[X ⨂ Y ⨂ Z, X ⨂ (Y ⨂ Z)](P.associate[X, Y, Z]))
    def diassociate[X: TC, Y: TC, Z: TC]: PlayCat1[->, F, X ⨂ (Y ⨂ Z), X ⨂ Y ⨂ Z] =
      PlayCat1(F.map[X ⨂ (Y ⨂ Z), X ⨂ Y ⨂ Z](P.diassociate[X, Y, Z]))
  }

  trait MonoPlayCatConj[->[_,_], ⨂[_,_], T[_], F[_], I] extends AssocPlayCatConj[->,⨂,T,F]
    with  Monoidal[PlayCat1[->, F,*,*], ⨂]
  {
    type Id = I
    protected def P: Monoidal.Aux[->, ⨂, T, I]
    def idl  [A: TC]: PlayCat1[->, F, Id ⨂ A, A] = PlayCat1(F.map[Id ⨂ A, A](P.idl))
    def coidl[A: TC]: PlayCat1[->, F, A, Id ⨂ A] = PlayCat1(F.map[A, Id ⨂ A](P.coidl))
    def idr  [A: TC]: PlayCat1[->, F, A ⨂ Id, A] = PlayCat1(F.map[A ⨂ Id, A](P.idr))
    def coidr[A: TC]: PlayCat1[->, F, A, A ⨂ Id] = PlayCat1(F.map[A, A ⨂ Id](P.coidr))
  }

  trait BraidPlayCatConj[->[_,_], ⨂[_,_], T[_], F[_]] extends AssocPlayCatConj[->, ⨂, T, F] with Braided[PlayCat1[->, F,*,*], ⨂] {
    protected def P: Braided.Aux[->, ⨂, T]
    def braid[A: TC, B: TC]: PlayCat1[->, F, A ⨂ B, B ⨂ A] = PlayCat1(F.map[A ⨂ B, B ⨂ A](P.braid))
  }

  trait SymmPlayCatConj[->[_,_], ⨂[_,_], T[_], F[_]] extends BraidPlayCatConj[->, ⨂, T, F] with Symmetric[PlayCat1[->, F,*,*], ⨂] {
    protected def P: Symmetric.Aux[->, ⨂, T]
  }

  trait CartesianPlayCatConj[->[_,_], ⨂[_,_], T[_], F[_], I] extends MonoPlayCatConj[->, ⨂, T, F, I]
    with Cartesian[PlayCat1[->, F,*,*], ⨂]
  {
    protected def F: LaxSemigroupal[⨂, ->, ⨂, F] with Endofunctor[->, F]
    protected def P: Cartesian.Aux[->, ⨂, T, I]
    def fst[A: TC, B: TC]: PlayCat1[->, F, A ⨂ B, A] = PlayCat1(F.map(P.fst[A, B]))
    def snd[A: TC, B: TC]: PlayCat1[->, F, A ⨂ B, B] = PlayCat1(F.map(P.snd[A, B]))
    def diag[A: TC]: PlayCat1[->, F, A, A ⨂ A] = PlayCat1(F.map(P.diag[A]))
    def &&&[X, Y, Z](f: PlayCat1[->, F, X, Y], g: PlayCat1[->, F, X, Z]): PlayCat1[->, F, X, Y ⨂ Z] =
      PlayCat1(P.C.andThen(P.&&&(f.fn, g.fn), F.product[Y, Z]))
  }


}

import PlayCatHelpers._
trait PlayCatImplicits extends PlayCatImplicits01 {
  implicit def subcat[F[_]]: Subcat.Aux[PlayCat[F,*,*], Trivial.T1] = new SubcatPlayCat[F] {}

  implicit def bifunctorConj[F[_]](implicit
    LS: LaxSemigroupal[/\, * => *, /\, F],
    OS: OplaxSemigroupal[/\, * => *, /\, F]
  ): Endobifunctor[PlayCat[F,*,*], /\] =
    new Endobifunctor[PlayCat[F,*,*], /\] {
      def bimap[A, X, B, Y](left: PlayCat[F, A, X], right: PlayCat[F, B, Y]): PlayCat[F, A /\ B, X /\ Y] =
        PlayCat(OS.opProduct[A, B] >>> Endobifunctor[* => *, /\].bimap(left.fn, right.fn) >>> LS.product[X, Y])
    }

  implicit def bifunctorDisj[F[_]](implicit
    LS: LaxSemigroupal[\/, * => *, \/, F],
    OS: OplaxSemigroupal[\/, * => *, \/, F]
  ): Endobifunctor[PlayCat[F,*,*], \/] =
    new Endobifunctor[PlayCat[F,*,*], \/] {
      def bimap[A, X, B, Y](left: PlayCat[F, A, X], right: PlayCat[F, B, Y]): PlayCat[F, A \/ B, X \/ Y] =
        PlayCat(OS.opProduct[A, B] >>> Endobifunctor[* => *, \/].bimap(left.fn, right.fn) >>> LS.product[X, Y])
    }

  implicit def cartesianConj[F[_]](implicit
    FF: Endofunctor[* => *, F],
    LS: LaxSemigroupal[/\, * => *, /\, F],
    OS: OplaxSemigroupal[/\, * => *, /\, F]
  ): Cartesian.Aux[PlayCat[F,*,*], /\, Trivial.T1, Unit] =
    new CartesianPlayCatConj[F] {
      val F = FF;
      val L = LS; val bifunctor = implicitly }

  implicit def cartesianDisj[F[_]](implicit
    FF: Endofunctor[Dual[* => *,*,*], F],
    LS: LaxSemigroupal[\/, * => *, \/, F],
    OS: OplaxSemigroupal[\/, * => *, \/, F]
  ): Cocartesian.Aux[PlayCat[F,*,*], \/, Trivial.T1, Void] =
    new CocartesianPlayCatDisj[F] { val F = FF; val L = OS; val bifunctor = implicitly }

  implicit def distributive[F[_]](implicit
    FC: Endofunctor[* => *, F],
    FD: Endofunctor[Dual[* => *,*,*], F],
    LS: LaxSemigroupal[/\, * => *, /\, F],
    OS: OplaxSemigroupal[/\, * => *, /\, F],
    LS1: LaxSemigroupal[\/, * => *, \/, F],
    OS1: OplaxSemigroupal[\/, * => *, \/, F]
  ): Distributive.Aux[PlayCat[F,*,*], Trivial.T1, /\, Unit, \/, Void] =
    new DistribPlayCat[F] { val F = FC; val cartesian = implicitly; val cocartesian = implicitly }

  def tmp1[T[_]](implicit F: Endofunctor[* => *, T], L: LaxSemigroupal[/\, * => *, /\, T]): LaxSemigroupal[/\, * => *, /\, λ[a => (T[a], a)]] =
    new LaxSemigroupal[/\, * => *, /\, λ[a => (T[a], a)]] {
      def A = implicitly
      type TC1[a] = Trivial.T1[a]
      type TC2[a] = Trivial.T1[a]
      def M1: Associative.Aux[* => *, /\, Trivial.T1] = implicitly
      def M2: Associative.Aux[* => *, /\, Trivial.T1] = implicitly
      def map[A, B](f: A => B): ((T[A], A)) => (T[B], B) = { case (ta, a) => (F.map(f)(ta), f(a)) }
      def product[A, B]: (T[A], A) /\ (T[B], B) => (T[A /\ B], A /\ B) =
        p => (L.product[A, B](/\(p._1._1, p._2._1)), /\(p._1._2, p._2._2))
    }


  def tmp2[T[_]](implicit
    F: Endofunctor[* => *, T],
    L: OplaxSemigroupal[\/, * => *, \/, T]
  ): OplaxSemigroupal[\/, * => *, \/, λ[a => (T[a], a)]] =
    new OplaxSemigroupal[\/, * => *, \/, λ[a => (T[a], a)]] {
      def A = implicitly
      type TC1[a] = Trivial.T1[a]
      type TC2[a] = Trivial.T1[a]
      def M1: Associative.Aux[Dual[* => *,*,*], \/, Trivial.T1] = implicitly
      def M2: Associative.Aux[Dual[* => *,*,*], \/, Trivial.T1] = implicitly
      def map[A, B](f: Dual[* => *, A, B]): Dual[* => *, (T[A], A), (T[B], B)] =
        Dual({ case (ta, a) => (F.map(f)(ta), f(a)) })
      def product[A, B]: Dual[* => *, (T[A], A) \/ (T[B], B), (T[A \/ B], A \/ B)] = {
        Dual(p => {
          val pp: T[A \/ B] => T[A] \/ T[B] = L.opProduct[A, B]
          val x1: T[A] \/ T[B] = pp(p._1)
          val x2: A \/ B = p._2
          // ((A \/ B), (C \/ D)) => (A, C) \/ (B, D) Impossible!!!!!!!!
          val r: (T[A], A) \/ (T[B], B) = ???
          r
        })
      }

    }
}

trait PlayCatImplicits01 extends PlayCatImplicits02 {
}

trait PlayCatImplicits02 {
}

object PlayCatHelpers {
  trait SubcatPlayCat[F[_]] extends Subcat[PlayCat[F, *, *]] {
    type TC[a] = Trivial.T1[a]
    def id[A](implicit A: TC[A]): PlayCat[F, A, A] = PlayCat(identity)
    def andThen[A, B, C](ab: PlayCat[F, A, B], bc: PlayCat[F, B, C]): PlayCat[F, A, C] =
      PlayCat(ab.fn >>> bc.fn)
  }

  trait MonoSymmPlayCatConj[F[_]] extends Monoidal[PlayCat[F,*,*], /\] with Symmetric[PlayCat[F,*,*], /\] {
    type TC[a] = Trivial.T1[a]
    type Id = Unit
    protected def F: Endofunctor[* => *, F]
    def C: Subcat.Aux[PlayCat[F,*,*], TC] = implicitly
    def associate  [X: TC, Y: TC, Z: TC]: PlayCat[F, X /\ Y /\ Z, X /\ (Y /\ Z)] =
      PlayCat(F.map[X /\ Y /\ Z, X /\ (Y /\ Z)](p => /\(p._1._1, /\(p._1._2, p._2))))
    def diassociate[X: TC, Y: TC, Z: TC]: PlayCat[F, X /\ (Y /\ Z), X /\ Y /\ Z] =
      PlayCat(F.map[X /\ (Y /\ Z), X /\ Y /\ Z](p => /\(/\(p._1, p._2._1), p._2._2)))
    def braid[A: TC, B: TC]: PlayCat[F, A /\ B, B /\ A] = PlayCat(F.map[A /\ B, B /\ A](_.swap))
    def idl  [A: TC]: PlayCat[F, Unit /\ A, A] = PlayCat(F.map[Unit /\ A, A](_._2))
    def coidl[A: TC]: PlayCat[F, A, Unit /\ A] = PlayCat(F.map[A, Unit /\ A](/\((), _)))
    def idr  [A: TC]: PlayCat[F, A /\ Unit, A] = PlayCat(F.map[A /\ Unit, A](_._1))
    def coidr[A: TC]: PlayCat[F, A, A /\ Unit] = PlayCat(F.map[A, A /\ Unit](/\(_, ())))
  }

  trait CartesianPlayCatConj[F[_]] extends MonoSymmPlayCatConj[F] with Cartesian[PlayCat[F,*,*], /\] {
    protected def F: Endofunctor[* => *, F]
    protected def L: LaxSemigroupal[/\, * => *, /\, F]
    def fst[A: TC, B: TC]: PlayCat[F, A /\ B, A] = PlayCat(((ab: F[A /\ B]) => ab) >>> F.map(_._1))
    def snd[A: TC, B: TC]: PlayCat[F, A /\ B, B] = PlayCat(((ab: F[A /\ B]) => ab) >>> F.map(_._2))
    def diag[A: TC]: PlayCat[F, A, A /\ A] = PlayCat(((fa: F[A]) => /\(fa, fa)) >>> L.product[A, A])
    def &&&[X, Y, Z](f: PlayCat[F, X, Y], g: PlayCat[F, X, Z]): PlayCat[F, X, Y /\ Z] =
      PlayCat(Cartesian[* => *, /\].&&&(f.fn, g.fn) >>> L.product[Y, Z])
  }

  trait MonoSymmPlayCatDisj[F[_]] extends Monoidal[Dual[PlayCat[F,*,*],*,*], \/] with Symmetric[Dual[PlayCat[F,*,*],*,*], \/] {
    type TC[a] = Trivial.T1[a]
    type Id = Void
    protected def F: Endofunctor[Dual[* => *,*,*], F]
    def C: Subcat.Aux[Dual[PlayCat[F, *, *], *, *], TC] = implicitly
    def associate  [X:TC, Y: TC, Z: TC]: Dual[PlayCat[F, *, *], X \/ Y \/ Z, X \/ (Y \/ Z)] =
      Dual(PlayCat(F.map[X \/ Y \/ Z, X \/ (Y \/ Z)](Dual(Associative[* => *, \/].diassociate[X, Y, Z](trivialInstance, trivialInstance, trivialInstance)))))
    def diassociate[X:TC, Y: TC, Z: TC]: Dual[PlayCat[F, *, *], X \/ (Y \/ Z), X \/ Y \/ Z] =
      Dual(PlayCat(F.map[X \/ (Y \/ Z), X \/ Y \/ Z](Dual(Associative[* => *, \/].associate[X, Y, Z](trivialInstance, trivialInstance, trivialInstance)))))
    def idl  [A: TC]: Dual[PlayCat[F, *, *], Void \/ A, A] = Dual(PlayCat(F.map[Void \/ A, A](Dual(_.right[Void]))))
    def coidl[A: TC]: Dual[PlayCat[F, *, *], A, Void \/ A] = Dual(PlayCat(F.map[A, Void \/ A](Dual(_.fold(identity, identity)))))
    def idr  [A: TC]: Dual[PlayCat[F, *, *], A \/ Void, A] = Dual(PlayCat(F.map[A \/ Void, A](Dual(_.left[Void]))))
    def coidr[A: TC]: Dual[PlayCat[F, *, *], A, A \/ Void] = Dual(PlayCat(F.map[A, A \/ Void](Dual(_.fold(identity, identity)))))
    def braid[A: TC, B: TC]: Dual[PlayCat[F, *, *], A \/ B, B \/ A] = Dual(PlayCat(F.map[A \/ B, B \/ A](Dual(_.swap))))
  }

  trait CocartesianPlayCatDisj[F[_]] extends MonoSymmPlayCatDisj[F] with Cocartesian[PlayCat[F,*,*], \/] {
    protected def F: Endofunctor[Dual[* => *,*,*], F]
    protected def L: LaxSemigroupal[\/, Dual[* => *,*,*], \/, F]
    def fst[A: TC, B: TC]: Dual[PlayCat[F, *, *], A \/ B, A] = Dual(PlayCat(F.map[A \/ B, A](Dual(_.left[B])).toFn))
    def snd[A: TC, B: TC]: Dual[PlayCat[F, *, *], A \/ B, B] = Dual(PlayCat(F.map[A \/ B, B](Dual(_.right[A])).toFn))
    def diag[A: TC]: Dual[PlayCat[F, *, *], A, A \/ A] =
      Dual(PlayCat(L.product[A, A].toFn >>> Cocartesian[* => *, \/].diag[F[A]](trivialInstance).toFn))
    def &&&[X, Y, Z](f: Dual[PlayCat[F, *, *], X, Y], g: Dual[PlayCat[F, *, *], X, Z]): Dual[PlayCat[F, *, *], X, Y \/ Z] =
      Dual(PlayCat(L.product[Y, Z].toFn >>> Cocartesian[* => *, \/].|||(f.fn, g.fn)))
  }

  trait DistribPlayCat[F[_]] extends SubcatPlayCat[F] with Distributive[PlayCat[F,*,*], /\, \/] {
    type ProductId = Unit
    type SumId = Void
    protected def F: Endofunctor[* => *, F]
    def distribute[A: TC, B: TC, C: TC]: PlayCat[F, A /\ (B \/ C), A /\ B \/ (A /\ C)] =
      PlayCat(F.map[A /\ (B \/ C), A /\ B \/ (A /\ C)](p => p._2.fold(b => /\(p._1, b).left, c => /\(p._1, c).right)))
  }

}