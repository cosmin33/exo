package io.cosmo.exo.evidence

import io.cosmo.exo.*
import io.cosmo.exo.inhabitance.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.categories.Subcategory.Aux
import io.cosmo.exo.functors.*

sealed abstract class Is[A, B] { self =>
  def subst[F[_]](fa: F[A]): F[B]

  final def coerce(a: A): B = subst[[x] =>> x](a)

  final def apply(a: A): B = coerce(a)

  final def andThen[C](bc: B === C): A === C = bc.subst[[x] =>> A === x](self)

  final def compose[Z](za: Z === A): Z === B = za.andThen(self)

  final def flip: B === A = subst[[x] =>> x === A](Is.refl)

  final def lift[F[_]]: F[A] === F[B] = Is.lift[F, A, B](self)

  def lift2[F[_,_]]: [I,J] => (I === J) => F[A,I] === F[B,J] = [I,J] => (ij: I === J) => Is.lift2[F](self, ij)

  def onF[X](fa: X => A): X => B = subst[[o] =>> X => o](fa)

  def toPredef: A =:= B = subst[[o] =>> A =:= o](summon[A =:= A])

  def toIso: A <=> B = subst[[o] =>> A <=> o](Iso.refl[A])

  def toAs: A <~< B = subst[[x] =>> A <~< x](As.refl[A])

}

object Is {
  def apply[A, B](using ev: A === B): A === B = ev
  def from[A, B](fn: [F[_]] => F[A] => F[B]): A === B =
    new Is[A, B]:
      def subst[F[_]](fa: F[A]): F[B] = fn(fa)

  given refl[A]: Is[A, A] with
    def subst[F[_]](fa: F[A]): F[A] = fa

  given isoCanonic[A, B]: (([F[_]] => F[A] => F[B]) <=> (A === B)) =
    <=>.unsafe(Is.from(_), is => [F[_]] => (fa: F[A]) => is.subst[F](fa))

  def lift[F[_], A, B](ab: A === B): F[A] === F[B] = ab.subst[[a] =>> F[A] === F[a]](refl)
  
  def lift2[F[_, _]] = new LiftHelper[F]; final class LiftHelper[F[_, _]] {
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

  def lift4[F[_, _, _, _], A, X, B, Y, C, Z, D, T]
  (ax: A === X, by: B === Y, cz: C === Z, dt: D === T): F[A, B, C, D] === F[X, Y, Z, T] = {
    type f1[α] = F[A, B, C, D] === F[α, B, C, D]
    type f2[α] = F[A, B, C, D] === F[X, α, C, D]
    type f3[α] = F[A, B, C, D] === F[X, Y, α, D]
    type f4[α] = F[A, B, C, D] === F[X, Y, Z, α]
    dt.subst[f4](cz.subst[f3](by.subst[f2](ax.subst[f1](refl))))
  }

  def fromPredef[A, B](eq: A =:= B): A === B = Axioms.predefEq(eq)

  def lem[A, B]: ¬¬[(A =!= B) \/ (A === B)] =
    ¬¬.lem[A === B].map(_.fold(
      neq => -\/[A =!= B, A === B](=!=.witness(neq)),
      r => \/-[A =!= B, A === B](r)
    ))


  def consistent[A, B](f: (A =!= B) => Void): A === B =
    proposition[A, B].proved(using ¬¬.witness(a => f(WeakApart.witness(a))))

  given proposition[A, B]: Proposition[Is[A, B]] =
    Proposition.witness((p: ¬¬[Is[A, B]]) => Axioms.isConsistency[A, B](p))

  given groupoid: Groupoid[===] with Concrete[===] with
    type TC[a] = Trivial[a]
    def id[A: TC]: A === A = refl
    def andThen[A, B, C](ab: A === B, bc: B === C): A === C = ab.andThen(bc)
    def flip[A, B](ab: A === B): B === A = ab.flip
    def concretize[A, B](f: A === B): (A, TC[A]) => (B, TC[B]) = (a, _) => (f(a), Trivial[B])

  given monoidalIntersect: Monoidal.Proto[===, &, Trivial, Any] with Symmetric.Proto[===, &, Trivial] with
    def C: Subcat.Aux[===, Trivial] = summon
    def bifunctor: Endobifunctor[===, &] = summon
    def associate  [X: TC, Y: TC, Z: TC]: ((X & Y) & Z) === (X & (Y & Z)) = summon
    def diassociate[X: TC, Y: TC, Z: TC]: (X & (Y & Z)) === ((X & Y) & Z) = summon
    def idl  [A: TC]: (Any & A) === A = summon
    def idr  [A: TC]: (A & Any) === A = summon
    def coidl[A: TC]: A === (Any & A) = summon
    def coidr[A: TC]: A === (A & Any) = summon
    def braid[A: TC, B: TC]: (A & B) === (B & A) = summon

  given monoidalUnion: Monoidal.Proto[===, |, Trivial, Nothing] with Symmetric.Proto[===, |, Trivial] with
    def C: Subcat.Aux[===, Trivial] = summon
    def bifunctor: Endobifunctor[===, |] = summon
    def associate  [X: TC, Y: TC, Z: TC]: ((X | Y) | Z) === (X | (Y | Z)) = summon
    def diassociate[X: TC, Y: TC, Z: TC]: (X | (Y | Z)) === ((X | Y) | Z) = summon
    def idl  [A: TC]: (Nothing | A) === A = summon
    def idr  [A: TC]: (A | Nothing) === A = summon
    def coidl[A: TC]: A === (Nothing | A) = summon
    def coidr[A: TC]: A === (A | Nothing) = summon
    def braid[A: TC, B: TC]: (A | B) === (B | A) = summon

  given isoInjectivity[F[_] : IsInjective, A, B]: ((F[A] === F[B]) <=> (A === B)) =
    Iso.unsafe(IsInjective[F].apply(using _), _.lift)

  given universalFunctor[F[_]]: Endofunctor[===, F] = Exo.unsafe[===, ===, F]([a,b] => (f: a === b) => Is.lift(f))

  given universalBifunctor[F[_,_]]: Endobifunctor[===, F] = new Exobifunctor[===, ===, ===, F]:
    def bimap[A, B, C, D](ab: A === B, cd: C === D): F[A, C] === F[B, D] = Is.lift2(ab, cd)

}