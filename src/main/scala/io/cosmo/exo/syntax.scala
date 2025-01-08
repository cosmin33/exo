package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*

object syntax:
  extension[A](a: A)
    def isoTo[B](using iso: HasIso[Function, A, B]): B = iso.to(a)
    def left [B]: A \/ B = \/.left(a)
    def right[B]: B \/ A = \/.right(a)

  extension[F[_], A](fa: F[A])
    def emap  [==>[_,_], B](f: A ==> B)(using E: Exo.Cov[==>, F]): F[B] = E.map(f)(fa)
    def ecomap[==>[_,_], B](f: B ==> A)(using E: Exo.Con[==>, F]): F[B] = E.map(Dual(f))(fa)

  extension[->[_,_], A, B] (self: A -> B)
    def andThen[D](that: B -> D)(using Semicategory[->]): A -> D = Semicategory[->].compose(that, self)
    def compose[X](that: X -> A)(using Semicategory[->]): X -> B = Semicategory[->].compose(self, that)
    def <<<[X](that: X -> A)(using Semicategory[->]): X -> B = compose(that)
    def >>>[D](that: B -> D)(using Semicategory[->]): A -> D = andThen(that)

    def flipped(using G: Groupoid[->]): B -> A = G.flip(self)

    def dual: Dual[->, B, A] = Dual(self)

    def associateR[X, Y, Z, TC[_]](using
      A: Associative.Aux[->, /\, TC], ev: B === ((X /\ Y) /\ Z), tx: TC[X], ty: TC[Y], tz: TC[Z]
    ): A -> (X /\ (Y /\ Z)) = A.C.andThen(ev.subst[[α] =>> A -> α](self), A.associate[X, Y, Z])
    def diassociateR[X, Y, Z, TC[_]](using
      A: Associative.Aux[->, /\, TC], ev: B === (X /\ (Y /\ Z)), tx: TC[X], ty: TC[Y], tz: TC[Z]
    ): A -> ((X /\ Y) /\ Z) = A.C.andThen(ev.subst[[α] =>> A -> α](self), A.diassociate[X, Y, Z])

    def braid[X, Y](using B: Braided[->, /\], ev: B === (X /\ Y), tx: B.TC[X], ty: B.TC[Y]): A -> (Y /\ X) =
      B.C.andThen(ev.subst[[b] =>> A -> b](self), B.braid[X, Y])

    def merge[D](fn: A -> D)(using c: Cartesian[->, /\]): A -> (D /\ B) = c.&&&(fn, self)
    def merge3[D, E](f1: A -> D, f2: A -> E)(using c: Cartesian[->, /\]): A -> (D /\ (E /\ B)) = c.&&&(f1, c.&&&(f2, self))
    def merge4[D, E, F](f1: A -> D, f2: A -> E, f3: A -> F)(using c: Cartesian[->, /\]): A -> (D /\ (E /\ (F /\ B))) =
      c.&&&(f1, c.&&&(f2, c.&&&(f3, self)))

    def split[D](fn: D -> B)(using c: Cocartesian[->, \/]): (A \/ D) -> B = c.|||(self, fn)
    def split3[D, E](f1: D -> B, f2: E -> B)(using c: Cocartesian[->, \/]): (A \/ (D \/ E)) -> B = c.|||(self, c.|||(f1, f2))
    def split4[D, E, F](f1: D -> B, f2: E -> B, f3: F -> B)(using c: Cocartesian[->, \/]): (A \/ (D \/ (E \/ F))) -> B =
      c.|||(self, c.|||(f1, c.|||(f2, f3)))

    def toFunction(using C: Concrete[->], tc: C.TC[A]): A => B = C.toFunction(self)
  
  extension[->[_,_], F[_], G[_]](self: ∀[[a] =>> F[a] -> G[a]])
    def andThen[H[_]](that: ∀[[a] =>> G[a] -> H[a]])(using SemicategoryK[->]): ∀[[a] =>> F[a] -> H[a]] = SemicategoryK[->].andThen(self, that)
    def compose[E[_]](that: ∀[[a] =>> E[a] -> F[a]])(using SemicategoryK[->]): ∀[[a] =>> E[a] -> G[a]] = SemicategoryK[->].andThen(that, self)
    def >>>[H[_]](that: ∀[[a] =>> G[a] -> H[a]])(using SemicategoryK[->]): ∀[[a] =>> F[a] -> H[a]] = SemicategoryK[->].andThen(self, that)
    def <<<[E[_]](that: ∀[[a] =>> E[a] -> F[a]])(using SemicategoryK[->]): ∀[[a] =>> E[a] -> G[a]] = SemicategoryK[->].andThen(that, self)
    
  extension[->[_,_], F[_,_], G[_,_]](self: ∀∀[[a,b] =>> F[a,b] -> G[a,b]])
    def andThen[H[_,_]](that: ∀∀[[a,b] =>> G[a,b] -> H[a,b]])(using SemicategoryK2[->]): ∀∀[[a,b] =>> F[a,b] -> H[a,b]] = SemicategoryK2[->].andThen(self, that)
    def compose[E[_,_]](that: ∀∀[[a,b] =>> E[a,b] -> F[a,b]])(using SemicategoryK2[->]): ∀∀[[a,b] =>> E[a,b] -> G[a,b]] = SemicategoryK2[->].andThen(that, self)
    def >>>[H[_,_]](that: ∀∀[[a,b] =>> G[a,b] -> H[a,b]])(using SemicategoryK2[->]): ∀∀[[a,b] =>> F[a,b] -> H[a,b]] = SemicategoryK2[->].andThen(self, that)
    def <<<[E[_,_]](that: ∀∀[[a,b] =>> E[a,b] -> F[a,b]])(using SemicategoryK2[->]): ∀∀[[a,b] =>> E[a,b] -> G[a,b]] = SemicategoryK2[->].andThen(that, self)
  
  extension[->[_,_], F[_[_]], G[_[_]]](self: ∀~[[a[_]] =>> F[a] -> G[a]])
    def andThen[H[_[_]]](that: ∀~[[a[_]] =>> G[a] -> H[a]])(using SemicategoryH[->]): ∀~[[a[_]] =>> F[a] -> H[a]] = SemicategoryH[->].andThen(self, that)
    def compose[E[_[_]]](that: ∀~[[a[_]] =>> E[a] -> F[a]])(using SemicategoryH[->]): ∀~[[a[_]] =>> E[a] -> G[a]] = SemicategoryH[->].andThen(that, self)
    def >>>[H[_[_]]](that: ∀~[[a[_]] =>> G[a] -> H[a]])(using SemicategoryH[->]): ∀~[[a[_]] =>> F[a] -> H[a]] = SemicategoryH[->].andThen(self, that)
    def <<<[E[_[_]]](that: ∀~[[a[_]] =>> E[a] -> F[a]])(using SemicategoryH[->]): ∀~[[a[_]] =>> E[a] -> G[a]] = SemicategoryH[->].andThen(that, self)
  
  extension[F[_,_], A, B](self: F[A, B])
    def bimapFn[C, D](f: A => C, g: B => D)(using F: Endobifunctor[* => *, F]): F[C, D] = F.bimap(f, g)(self)
    def bimap[==>[_,_], -->[_,_], C, D](f: A ==> C, g: B --> D)(using F: Exobifunctor[==>, -->, * => *, F]): F[C, D] = 
      F.bimap(f, g)(self)
