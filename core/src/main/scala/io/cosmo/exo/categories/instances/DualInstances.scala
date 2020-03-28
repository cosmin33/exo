package io.cosmo.exo.categories.instances

import io.cosmo.exo.categories._

import DualHelpers._
trait DualInstances extends DualInstances01 {
  def dualSubcat[->[_,_], C[_]](s: Subcat.Aux[->, C]): Subcat.Aux[Dual[->,*,*], C] =
    Dual.leibniz[->].subst[Subcat.Aux[*[_,_], C]](oppSubcat(s))

  def dualEndobifunctor[->[_,_], P[_,_]](e: Endobifunctor[->, P]): Endobifunctor[Dual[->,*,*], P] =
    Dual.leibniz[->].subst[Endobifunctor[*[_,_], P]](oppEndobifunctor(e))

  def dualSymmetric[->[_,_], P[_,_], C[_]](s: Symmetric.Aux[->, P, C]): Symmetric.Aux[Dual[->,*,*], P, C] =
    Dual.leibniz[->].subst[Symmetric.Aux[*[_,_], P, C]](oppSymmetric(s))

  def dualMonoidal[->[_,_], P[_,_], C[_], I](m: Monoidal.Aux[->, P, C, I]): Monoidal.Aux[Dual[->,*,*], P, C, I] =
    Dual.leibniz[->].subst[Monoidal.Aux[*[_,_], P, C, I]](oppMonoidal(m))
}

trait DualInstances01 extends DualInstances02 {
  def dualBraided[->[_,_], P[_,_], C[_]](b: Braided.Aux[->, P, C]): Braided.Aux[Dual[->,*,*], P, C] =
    Dual.leibniz[->].subst[Braided.Aux[*[_,_], P, C]](oppBraided(b))

  def dualSemicategory[->[_,_]](s: Semicategory[->]): Semicategory[Dual[->,*,*]] =
    Dual.leibniz[->].subst[Semicategory](oppSemicategory(s))
}

trait DualInstances02 extends DualInstances03 {
  def dualAssociative[->[_,_], P[_,_], C[_]](a: Associative.Aux[->, P, C]): Associative.Aux[Dual[->,*,*], P, C] =
    Dual.leibniz[->].subst[Associative.Aux[*[_,_], P, C]](oppAssociative(a))
}

trait DualInstances03 {

}

private[instances] object DualHelpers {
  private[instances] def oppSemicategory[->[_,_]](s: Semicategory[->]): Semicategory[Opp[->]#l] =
    new OppSemicategory[->] {val S = s}

  private[instances] def oppSubcat[->[_,_], C[_]](s: Subcat.Aux[->, C]): Subcat.Aux[Opp[->]#l, C] =
    new OppSubcat[->, C] {val S = s}

  private[instances] def oppEndobifunctor[->[_,_], P[_,_]](e: Endobifunctor[->, P]): Endobifunctor[Opp[->]#l, P] =
    new OppBifunctor[->, P] {val E = e}

  private[instances] def oppAssociative[->[_,_], P[_,_], C[_]](a: Associative.Aux[->, P, C]): Associative.Aux[Opp[->]#l, P, C] =
    new OppAssociative[->, P, C] {val A = a}

  private[instances] def oppBraided[->[_,_], P[_,_], C[_]](b: Braided.Aux[->, P, C]): Braided.Aux[Opp[->]#l, P, C] =
    new OppBraided[->, P, C] {val A = b}

  private[instances] def oppSymmetric[->[_,_], P[_,_], C[_]](b: Symmetric.Aux[->, P, C]): Symmetric.Aux[Opp[->]#l, P, C] =
    new OppBraided[->, P, C] with Symmetric[Opp[->]#l, P] {val A = b}

  private[instances] def oppMonoidal[->[_,_], P[_,_], C[_], I](m: Monoidal.Aux[->, P, C, I]): Monoidal.Aux[Opp[->]#l, P, C, I] =
    new OppMonoidal[->, P, C, I] {val A = m}

  trait OppSemicategory[->[_,_]] extends Semicategory[Opp[->]#l] {
    protected def S: Semicategory[->]
    override def andThen[X, Y, Z](ab: Y -> X, bc: Z -> Y): Z -> X = S.andThen(bc, ab)
  }

  trait OppSubcat[->[_,_], C[_]]
    extends OppSemicategory[->]
    with Subcat[Opp[->]#l]
  {
    type TC[a] = C[a]
    protected def S: Subcat.Aux[->, C]
    override def id[A](implicit A: TC[A]): A -> A = S.id[A]
  }

  trait OppBifunctor[->[_,_], P[_,_]] extends Endobifunctor[Opp[->]#l, P] {
    protected def E: Endobifunctor[->, P]
    def L = oppSemicategory(E.L)
    def R = oppSemicategory(E.R)
    def C = oppSemicategory(E.C)
    def leftMap [A, B, Z](fn:  Z -> A): P[Z, B] -> P[A, B] = E.leftMap(fn)
    def rightMap[A, B, Z](fn:  Z -> B): P[A, Z] -> P[A, B] = E.rightMap(fn)
    override def bimap[A, X, B, Y](left: X -> A, right: Y -> B): P[X, Y] -> P[A, B] = E.bimap(left, right)
  }

  trait OppAssociative[->[_,_], P[_,_], C[_]] extends Associative[Opp[->]#l, P] {
    protected def A: Associative.Aux[->, P, C]
    type TC[a] = C[a]
    def C = oppSubcat[->, C](A.C)
    def bifunctor = oppEndobifunctor(A.bifunctor)
    def associate  [X, Y, Z]: P[X, P[Y, Z]] -> P[P[X, Y], Z] = A.diassociate
    def diassociate[X, Y, Z]: P[P[X, Y], Z] -> P[X, P[Y, Z]] = A.associate
  }

  trait OppBraided[->[_,_], P[_,_], C[_]] extends OppAssociative[->, P, C] with Braided[Opp[->]#l, P] {
    protected def A: Braided.Aux[->, P, C]
    def braid[A, B]: P[B, A] -> P[A, B] = A.braid
  }

  trait OppMonoidal[->[_,_], P[_,_], C[_], I] extends OppAssociative[->, P, C] with Monoidal[Opp[->]#l, P] {
    type Id = I
    protected def A: Monoidal.Aux[->, P, C, I]
    def idl[A]: A -> P[I, A] = A.coidl
    def coidl[A]: P[I, A] -> A = A.idl
    def idr[A]: A -> P[A, I] = A.coidr
    def coidr[A]: P[A, I] -> A = A.idr
  }

  trait OppCartesian[->[_,_], P[_,_], C[_], I] extends OppMonoidal[->, P, C, I] with Cartesian[Opp[->]#l, P] {
    protected def A: Cartesian.Aux[->, P, C, I]
    def fst[A, B]: A -> P[A, B] = ???
    def snd[A, B]: B -> P[A, B] = ???
    def diag[A]: P[A, A] -> A = ???
    def &&&[X, Y, Z](f: Y -> X, g: Z -> X): P[Y, Z] -> X = ???
    def braid[A, B]: P[B, A] -> P[A, B] = ???
  }

}