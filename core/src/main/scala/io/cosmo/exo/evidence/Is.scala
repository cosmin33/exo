package io.cosmo.exo.evidence

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.categories.{Dual, Endobifunctor, Endofunctor, Groupoid, Semicategory, Subcat, Trivial}
import io.estatico.newtype.Coercible

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

  def toPredef: A =:= B = subst[A =:= *](implicitly[A =:= A])

  def toIso: A <=> B = subst[A <=> *](Iso.refl[A])

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

  implicit def coercibleToEquality[A, B](implicit ec: Coercible[A === A, A === B]): A === B = ec(Is.refl)

  implicit def exoCov[A]: Exo.Cov[===, A === *] = Exo.unsafe[===, * => *, A === *](_.subst[A === *])
  implicit def exoCon[A]: Exo.Con[===, * === A] = Exo.unsafe[Dual[===,*,*], * => *, * === A](_.flip.subst[* === A])

  implicit def faExoCov: ∀[λ[a => Exo.Cov[===, a === *]]] = ∀.of[λ[a => Exo.Cov[===, a === *]]].from(exoCov)
  implicit def faExoCon: ∀[λ[a => Exo.Con[===, * === a]]] = ∀.of[λ[a => Exo.Con[===, * === a]]].from(exoCon)

  implicit def leibnizFunctor[F[_]]: Endofunctor[===, F] = Exo.unsafe[===, ===, F](f => Is.lift(f))
  implicit def leibnizFunctorFn[F[_]]: Exo.Cov[===, F] = Exo.unsafe[===, * => *, F](f => Is.lift(f).apply(_))
  implicit def leibnizFunctorCn[F[_]]: Exo.Con[===, F] = Exo.unsafe[Dual[===,*,*], * => *, F](f => Is.lift(f.flip).apply(_))

  implicit def leibnizBifunctor[P[_,_]]: Endobifunctor[===, P] = new Endobifunctor[===, P] {
    override def bimap[A, X, B, Y](left: A === X, right: B === Y): P[A, B] === P[X, Y] = left.lift2[P](right)
  }

  private final class Refl[A]() extends Is[A, A] {
    def subst[F[_]](fa: F[A]): F[A] = fa
  }
  private val refl_ : ∀[Refl] = ∀.of[Refl].from(new Refl())

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

  def lift4[F[_,_,_,_], A, X, B, Y, C, Z, D, T]
  (ax: A === X, by: B === Y, cz: C === Z, dt: D === T): F[A, B, C, D] === F[X, Y, Z, T] = {
    type f1[α] = F[A, B, C, D] === F[α, B, C, D]
    type f2[α] = F[A, B, C, D] === F[X, α, C, D]
    type f3[α] = F[A, B, C, D] === F[X, Y, α, D]
    type f4[α] = F[A, B, C, D] === F[X, Y, Z, α]
    dt.subst[f4](cz.subst[f3](by.subst[f2](ax.subst[f1](refl))))
  }

  def fromPredef[A, B](eq: A =:= B): A === B = Axioms.predefEq(eq)

  implicit def proposition[A, B]: Proposition[Is[A, B]] =
    (p: ¬¬[Is[A, B]]) => Axioms.isConsistency[A, B](p.run)


  def lem[A, B]: ¬¬[(A =!= B) \/ (A === B)] =
    ¬¬.lem[A === B].map(_.fold(
      neq => left[A =!= B, A === B](=!=.witness(neq.run)),
      r => right[A =!= B, A === B](r)
    ))

  def consistent[A, B](f: (A =!= B) => Void): A === B =
    proposition[A, B].proved(¬¬.witness(a => f(WeakApart.witness(a))))

}

trait IsInstances extends IsInstances01 {
  implicit def eqLift1[F[_], A, X](implicit eq: A === X): F[A] === F[X] = Is.lift(eq)
  implicit def eqKLift1[A[_[_]], F[_], F1[_]](implicit eq: F =~= F1): A[F] === A[F1] = =~=.lower(eq)
  implicit def eqK2Lift1[A[_[_,_]], F[_,_], F1[_,_]](implicit eq: F =~~= F1): A[F] === A[F1] = =~~=.lower(eq)
}
trait IsInstances01 extends IsInstances02 {
  implicit def eqLift2[F[_,_], A, X, B, Y](implicit e1: A === X, e2: B === Y): F[A, B] === F[X, Y] = Is.lift2(e1, e2)
  implicit def eqKLift2[A[_[_],_[_]], F[_], F1[_], G[_], G1[_]](implicit
    e1: F =~= F1, e2: G =~= G1
  ): A[F, G] === A[F1, G1] = =~=.lower2(e1, e2)
  implicit def eqK2Lift2[A[_[_,_], _[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1
  ): A[F, G] === A[F1, G1] = =~~=.lower2.on(e1, e2)
}
trait IsInstances02 extends IsInstances03 {
  implicit def eqLift3[F[_,_,_], A, X, B, Y, C, Z](implicit e1: A === X, e2: B === Y, e3: C === Z): F[A, B, C] === F[X, Y, Z] = Is.lift3(e1, e2, e3)
  implicit def eqKLift3[A[_[_],_[_],_[_]], F[_], F1[_], G[_], G1[_], H[_], H1[_]](implicit
    e1: F =~= F1, e2: G =~= G1, e3: H =~= H1
  ): A[F, G, H] === A[F1, G1, H1] = =~=.lower3(e1, e2, e3)
  implicit def eqK2Lift3[A[_[_,_],_[_,_],_[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1, e3: H =~~= H1
  ): A[F, G, H] === A[F1, G1, H1] = =~~=.lower3.on(e1, e2, e3)
}
trait IsInstances03 extends IsInstances04 {
  implicit def eqLift4[F[_,_,_,_], A, X, B, Y, C, Z, D, T](implicit e1: A === X, e2: B === Y, e3: C === Z, e4: D === T): F[A, B, C, D] === F[X, Y, Z, T] = Is.lift4(e1, e2, e3, e4)
  implicit def eqKLift4[A[_[_],_[_],_[_],_[_]], F[_], F1[_], G[_], G1[_], H[_], H1[_], I[_], I1[_]](implicit
    e1: F =~= F1, e2: G =~= G1, e3: H =~= H1, e4: I =~= I1
  ): A[F, G, H, I] === A[F1, G1, H1, I1] = =~=.lower4(e1, e2, e3, e4)
  implicit def eqK2Lift4[A[_[_,_],_[_,_],_[_,_],_[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_], I[_,_], I1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1, e3: H =~~= H1, e4: I =~~= I1
  ): A[F, G, H, I] === A[F1, G1, H1, I1] = =~~=.lower4.on(e1, e2, e3, e4)
}
trait IsInstances04 {
  implicit def eqK2Lift5[A[_[_,_],_[_,_],_[_,_],_[_,_],_[_,_]], F[_,_], F1[_,_], G[_,_], G1[_,_], H[_,_], H1[_,_], I[_,_], I1[_,_], J[_,_], J1[_,_]](implicit
    e1: F =~~= F1, e2: G =~~= G1, e3: H =~~= H1, e4: I =~~= I1, e5: J =~~= J1
  ): A[F, G, H, I, J] === A[F1, G1, H1, I1, J1] = =~~=.lower5.on(e1, e2, e3, e4, e5)
}
