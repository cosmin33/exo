package io.cosmo.exo.categories.functors

import cats.{Contravariant, Functor, Id, Invariant}
import io.cosmo.exo
import io.cosmo.exo._
import io.cosmo.exo.categories.Trivial.T1
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.data.{KleisModule, ProdCat}
import io.cosmo.exo.categories.data.ProdCat.Dicat
import io.cosmo.exo.evidence._
import io.cosmo.exo.typeclasses.{HasTc, TypeF}
import shapeless.the

trait Exofunctor[==>[_,_], -->[_,_], F[_]] {
  type TC1[_]
  def C : Subcat.Aux[==>, TC1]

  type TC2[_]
  def D : Subcat.Aux[-->, TC2]

  def map[A, B](f: A ==> B): F[A] --> F[B]
}

object Exofunctor {
  type Aux[==>[_,_], -->[_,_], F[_], =>#[_], ->#[_]] =
    Exofunctor[==>, -->, F] {type TC1[A] = =>#[A]; type TC2[A] = ->#[A]}
  type AuxT[==>[_,_], -->[_,_], F[_]] = Aux[==>, -->, F, Trivial.T1, Trivial.T1]

  type Cov[->[_,_], F[_]] = Exofunctor[->, * => *, F]
  /** This is isomorphic with cats.Covariant */
  type CovF[F[_]] = Cov[* => *, F]

  type Con[->[_,_], F[_]] = Exofunctor[Dual[->,*,*], * => *, F]
  /** This is isomorphic with cats.Contravariant */
  type ConF[F[_]] = Con[* => *, F]

  type Inv[->[_,_], F[_]] = Exofunctor[Dicat[->,*,*], * => *, F]
  /** This is isomorphic with cats.Invariant */
  type InvF[F[_]] = Inv[* => *, F]

  //type Pha[->[_,_], F[_]] = Exofunctor[]

  /** Exofunctor from an isomorphism category to Function1 */
  type IsoFun[->[_,_], F[_]] = Exofunctor[Iso[->,*,*], * => *, F]

  /** Map on (A <-> B) gives you typeclass derivation: {{{HasTc[TC, A] => HasTc[TC, B]}}} */
  //type IsoTypeclass[->[_,_], TC[_[_]]] = IsoFun[->, HasTc[TC, *]]

//  type Traverse1[M[_], F[_]] = KleisModule.[]

  case class SingleOf[T, U <: {type TC1[_]; type TC2[_]}](widen: T {type TC1[a] = U#TC1[a]; type TC2[a] = U#TC2[a]})
  object SingleOf {
    implicit def mkSingleOf[T <: {type TC1[_]; type TC2[_]}](implicit t: T): SingleOf[T, t.type] = SingleOf(t)
  }

  trait Proto[|=>[_,_], -->[_,_], F[_], =>#[_], ->#[_]] extends
    Exofunctor[|=>, -->, F] {type TC1[A] = =>#[A]; type TC2[A] = ->#[A]}

  def unsafe[==>[_,_], -->[_,_], F[_], =>#[_], ->#[_]](
    fn: Exomap[==>, -->, F]
  )(implicit
    c1: Subcat.Aux[==>, =>#],
    c2: Subcat.Aux[-->, ->#],
  ): Exofunctor.Aux[==>, -->, F, =>#, ->#] =
    new Exofunctor[==>, -->, F] {
      type TC1[a] = =>#[a]
      type TC2[a] = ->#[a]
      val C = c1
      val D = c2
      def map[A, B](f: A ==> B): F[A] --> F[B] = fn.apply(f)
    }
  def unsafeTCov[F[_]](fn: Exomap[* => *, * => *, F]): Aux[Function, Function, F, T1, T1] = unsafe(fn)
  def unsafeTCon[F[_]](fn: Exomap[Dual[* => *,*,*], * => *, F]): Aux[Dual[* => *,*,*], * => *, F, T1, T1] = unsafe(fn)

  // TODO: de implementat:
//  type IsInvariantFunctor[F[_]]           = Exofunctor.AuxT[=!=, >~<, F]
//  type IsCovariantFunctor[F[_]]           = Endofunctor.AuxT[<~<, F]
//  type IsContravariantFunctor[F[_]]       = Exofunctor.AuxT[<~<, Opp[<~<]#l, F]
//  type IsConstantFunctor[F[_]]            = Exofunctor.AuxT[Trivial.T11, ===, F] // cam stupid
//  type LiskovBracketFunctor[F[_]]         = Exofunctor.AuxT[Dicat[<~<,*,*], ===, F]

  def toFn[==>[_, _], -->[_, _], F[_], =>#[_], ->#[_]](
    fun: Exofunctor.Aux[==>, -->, F, =>#, ->#]
  ): Exomap[==>, -->, F] = ∀∀.mk[Exomap[==>, -->, F]].from(fun.map)

  implicit def isoContravariant[F[_]]: Exofunctor.ConF[F] <=> Contravariant[F] =
    Iso.unsafe(
      F => new Contravariant[F] { def contramap[A, B](fa: F[A])(f: B => A): F[B] = F.map[A, B](Dual(f))(fa) },
      F => unsafeTCon(∀∀.of[λ[(a,b) => Dual[* => *, a, b] => F[a] => F[b]]].from(ba => F.contramap(_)(ba)))
    )

  implicit def isoInvariant[F[_]]: Exofunctor.InvF[F] <=> Invariant[F] =
    Iso.unsafe(
      F => new Invariant[F] {
             def imap[A, B](fa: F[A])(f: A => B)(g: B => A): F[B] = F.map(Dicat(f, g))(fa)
           },
      I => new Exofunctor[Dicat[* => *, *, *], * => *, F] {
             type TC1[a] = Trivial.T1[a]
             type TC2[a] = Trivial.T1[a]
             def C = ProdCat.categorySameTC
             def D = the[Subcat.Aux[* => *, Trivial.T1]]
             def map[A, B](f: Dicat[Function, A, B]) = I.imap(_)(f.first)(f.second)
           }
    )

  implicit def isoCovariant[F[_]]: Endofunctor.CovF[F] <=> Functor[F] =
    Iso.unsafe(
      F => new Functor[F] { def map[A, B](fa: F[A])(f: A => B): F[B] = F.map[A, B](f)(fa) },
      F => Exofunctor.unsafeTCov(∀∀.mk[Endomap[* => *, F]].from(ab => F.map(_)(ab)))
    )

}

object Endofunctor {
  type Aux[->[_,_], F[_], C[_]] = Exofunctor.Aux[->, ->, F, C, C]
  type AuxT[->[_,_], F[_]] = Aux[->, F, Trivial.T1]

  /** This is isomorphic with cats.Functor[F] */
  type CovF[F[_]] = Aux[* => *, F, Trivial.T1]
  trait Proto[->[_,_], F[_], C[_]] extends Exofunctor.Proto[->, ->, F, C, C]
  trait ProtoT[->[_,_], F[_]] extends Exofunctor.Proto[->, ->, F, Trivial.T1, Trivial.T1]
  trait ProtoA[->[_,_], F[_]] extends Exofunctor[->, ->, F] {type TC2[ᵒ] = TC1[ᵒ]}

  def unsafe[->[_,_], F[_], =>#[_]](
    fn: Exomap[->, ->, F]
  )(implicit
    c1: Subcat.Aux[->, =>#],
  ): Endofunctor.Aux[->, F, =>#] = Exofunctor.unsafe(fn)

  // e buna dar poate nu trebuie (daca unsafe simplu face fata la toate situatiile)
  //  def unsafeT[F[_]](fn: Exomap[* => *, * => *, F]) = unsafe[* => *, F, Trivial.T1](fn)

}

trait Exorepresentable[==>[_,_], ->[_,_], F[_]] {
  type Representation
  def functor: Exofunctor[==>, ->, F]
  def index   [A]: F[A] -> (Representation ==> A)
  def tabulate[A]: (Representation ==> A) -> F[A]

  private type <->[a,b] = Iso[->,a,b]
  def iso[A]: (Representation ==> A) <-> F[A] = Iso.unsafe(tabulate[A], index[A])(functor.D)
}
