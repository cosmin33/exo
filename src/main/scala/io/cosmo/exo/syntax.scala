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

    def associateR[X, Y, Z, ⊙[_,_], TC[_]](using
      A: Associative.Aux[->, ⊙, TC], ev: B === ⊙[⊙[X, Y], Z], tx: TC[X], ty: TC[Y], tz: TC[Z]
    ): A -> ⊙[X, ⊙[Y, Z]] = A.C.andThen(ev.subst[[α] =>> A -> α](self), A.associate[X, Y, Z])
    def diassociateR[X, Y, Z, ⊙[_,_], TC[_]](using
      A: Associative.Aux[->, ⊙, TC], ev: B === ⊙[X, ⊙[Y, Z]], tx: TC[X], ty: TC[Y], tz: TC[Z]
    ): A -> ⊙[⊙[X, Y], Z] = A.C.andThen(ev.subst[[α] =>> A -> α](self), A.diassociate[X, Y, Z])

    def braid[X, Y, ⊙[_,_]](using B: Braided[->, ⊙], ev: B === ⊙[X, Y], tx: B.TC[X], ty: B.TC[Y]
    ): A -> ⊙[Y, X] = B.C.andThen(ev.subst[[b] =>> A -> b](self), B.braid[X, Y])

    def split[⊙[_, _], D](fn: D -> B)(using c: Cocartesian[->, ⊙]): ⊙[A, D] -> B = c.|||(self, fn)
    def split3[⊙[_, _], D, E](f1: D -> B, f2: E -> B)(using c: Cocartesian[->, ⊙]): ⊙[A, ⊙[D, E]] -> B = c.|||(self, c.|||(f1, f2))

    def merge[⊙[_, _], D](fn: A -> D)(using c: Cartesian[->, ⊙]): A -> ⊙[D, B] = c.&&&(fn, self)
    def merge3[⊙[_, _], D, E](f1: A -> D, f2: A -> E)(using c: Cartesian[->, ⊙]): A -> ⊙[D, ⊙[E, B]] = c.&&&(f1, c.&&&(f2, self))

    def toFunction(using C: Concrete[->], tc: C.TC[A]): A => B = C.toFunction(self)

  extension[F[_,_], A, B](self: F[A, B])
    def bimapFn[C, D](f: A => C, g: B => D)(using F: Endobifunctor[* => *, F]): F[C, D] = F.bimap(f, g)(self)
    
//    def exobimap[==>[_,_], -->[_,_], C, D](f: A ==> C, g: B --> D)(using
//      F: Exobifunctor[==>, -->, * => *, F]
//    ): F[C, D] = F.bimap(f, g)(self)
