package io.cosmo.exo.evidence

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.categories.{Dual, Endobifunctor, Endofunctor, Groupoid, Semicategory, Subcat, Trivial}
import shapeless.the

sealed abstract class Is[A, B] private[Is]()  { ab =>
  import Is._

  def subst[F[_]](fa: F[A]): F[B]

  def apply(a: A): B = coerce(a)

  def coerce(a: A): B = subst[λ[a => a]](a)

  final def andThen[C](bc: B === C): A === C = bc.subst[A === *](ab)

  final def compose[Z](za: Z === A): Z === B = za.andThen(ab)

  final def flip: B === A = subst[* === A](refl)

  final def lift[F[_]]: F[A] === F[B] = Is.lift[F, A, B](ab)

  def lift2[F[_, _]] = new Lift2Helper[F]; final class Lift2Helper[F[_, _]] {
    def apply[I, J](ij: I === J): F[A, I] === F[B, J] = Is.lift2[F](ab, ij)
  }

  def onF[X](fa: X => A): X => B = subst[X => *](fa)

  def toPredef: A =:= B = subst[A =:= *](the[A =:= A])

  def toIso: <=>[A, B] = subst[A <=> *](Iso.refl[A])

  def toAs: A <~< B = subst[A <~< *](As.refl[A])
}

object Is extends IsInstances {
  def apply[A, B](implicit ev: A Is B): A Is B = ev

  implicit def isoCanonic[A, B]: ∀~[λ[f[_] => f[A] => f[B]]] <=> (A === B) =
    Iso.unsafe(
      fa => new Is[A, B] { def subst[F[_]](f: F[A]): F[B] = fa.apply[F](f) },
      ab => ∀~.of[λ[f[_] => f[A] => f[B]]].from(ab.subst)
    )

  implicit def isoInjectivity[F[_]: IsInjective, A, B]: (F[A] === F[B]) <=> (A === B) =
    Iso.unsafe(IsInjective[F].apply(_), _.lift)

  implicit def exoCov[A]: Exo.Cov[===, A === *] = Exo.unsafe[===, * => *, A === *](_.subst[A === *])
  implicit def exoCon[A]: Exo.Con[===, * === A] = Exo.unsafe[Dual[===,*,*], * => *, * === A](_.flip.subst[* === A])

  implicit def isBifunctor[P[_,_]]: Endobifunctor[===, P] = new Endobifunctor[===, P] {
    type TCL[a] = Trivial.T1[a]
    type TCR[a] = Trivial.T1[a]
    type TC [a] = Trivial.T1[a]
    val L, R, C = Semicategory.leibnizGroupoid
    override def bimap[A, X, B, Y](left: A === X, right: B === Y): P[A, B] === P[X, Y] = left.lift2[P](right)
    def leftMap [A, B, Z](fn: A === Z): P[A, B] === P[Z, B] = fn.lift[P[*, B]]
    def rightMap[A, B, Z](fn: B === Z): P[A, B] === P[A, Z] = fn.lift[P[A, *]]
  }

  private final class Refl[A]() extends Is[A, A] {
    def subst[F[_]](fa: F[A]): F[A] = fa
  }
  private val refl_ : ∀[Refl] = ∀.of[Refl](new Refl())

  implicit def refl[A]: A === A = refl_[A]

  def lift[F[_], A, B](ab: A === B): F[A] === F[B] = {
    type f[α] = F[A] === F[α]
    ab.subst[f](refl)
  }

  def lift2[F[_,_]] = new LiftHelper[F]; final class LiftHelper[F[_,_]] {
    def apply[A, B, I, J](ab: A === B, ij: I === J): F[A, I] === F[B, J] = {
      type f1[α] = F[A, I] === F[α, I]
      type f2[α] = F[A, I] === F[B, α]
      ij.subst[f2](ab.subst[f1](refl))
    }
  }

  def lift3[F[_, _, _], A, B, I, J, M, N]
  (ab: A === B, ij: I === J, mn: M === N): F[A, I, M] === F[B, J, N] = {
    type f1[α] = F[A, I, M] === F[α, I, M]
    type f2[α] = F[A, I, M] === F[B, α, M]
    type f3[α] = F[A, I, M] === F[B, J, α]
    mn.subst[f3](ij.subst[f2](ab.subst[f1](refl)))
  }

  def fromPredef[A, B](eq: A =:= B): A === B = Axioms.predefEq(eq)

  implicit def proposition[A, B]: Proposition[Is[A, B]] =
    (p: ¬¬[Is[A, B]]) => Axioms.isConsistency[A, B](p.run)


  def lem[A, B]: ¬¬[(A =!= B) \/ (A === B)] =
    ¬¬.lem[A === B].map(_.fold(
      neq => left[A =!= B, A === B](=!=.witness(neq.run)),
      r => right[A =!= B, A === B](r)
    ))
//  def lem[A, B]: ¬¬[Either[A =!= B, A === B]] = Inhabited.lem[A === B].map {
//    case Right(eqv) => Right(eqv)
//    case Left(neqv) => Left(WeakApart(neqv))
//  }

  def consistent[A, B](f: (A =!= B) => Void): A === B =
    proposition[A, B].proved(¬¬.witness(a => f(WeakApart.witness(a))))

  implicit def leibnizFunctor[F[_]](implicit
    cat: Semicategory[===],
  ): Endofunctor[===, F] =
    new Endofunctor[===, F] {
      val C, D = cat
      def map[A, B](f: A === B): F[A] === F[B] = Is.lift(f)
    }

}

trait IsInstances {
}