package io.cosmo.exo.internal

import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.functors._

trait DualInstances extends DualAssociativeInstances
  with DualSemicategoryInstances
  with DualBifunctorInstances
  
import DualHelpers._
trait DualSemicategoryInstances extends DualSemicategoryInstances01 {
  def oppSubcat[->[_,_], C[_]](s: Subcat.Aux[->, C]): Subcat.Aux[Opp[->]#l, C] =
    new OppSubcat[->, C] { val S = s }

  given dualSubcat[->[_,_], C[_]](using s: Subcat.Aux[->, C]): Subcat.Aux[Dual[->, *, *], C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Subcat.Aux[f, C]](oppSubcat(s))
}

trait DualSemicategoryInstances01 {
  def oppSemicat[->[_,_]](s: Semicategory[->]): Semicategory[Opp[->]#l] =
    new OppSemicategory[->] { val S = s }

  given dualSemicat[->[_,_]](using s: Semicategory[->]): Semicategory[Dual[->, *, *]] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Semicategory[f]](oppSemicat(s))
}

trait DualAssociativeInstances extends DualAssociativeInstances01 {
  def oppMonoidal[->[_,_], P[_,_], C[_], I](m: Monoidal.Aux[->, P, C, I]): Monoidal.Aux[Opp[->]#l, P, C, I] =
    new OppMonoidal[->, P, C, I] { val A = m }

  given dualMonoidal[->[_,_], P[_,_], C[_], I](using m: Monoidal.Aux[->, P, C, I]): Monoidal.Aux[Dual[->, *, *], P, C, I] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Monoidal.Aux[f, P, C, I]](oppMonoidal(m))
}

trait DualAssociativeInstances01 extends DualAssociativeInstances02 {
  def oppSymmetric[->[_,_], P[_,_], C[_]](s: Symmetric.Aux[->, P, C]): Symmetric.Aux[Opp[->]#l, P, C] =
    new Symmetric[Opp[->]#l, P] with OppBraided[->, P, C] { val A = s }

  given dualSymmetric[->[_,_], P[_,_], C[_]](using s: Symmetric.Aux[->, P, C]): Symmetric.Aux[Dual[->, *, *], P, C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Symmetric.Aux[f, P, C]](oppSymmetric(s))
}

trait DualAssociativeInstances02 extends DualAssociativeInstances03 {
  def oppBraided[->[_,_], P[_,_], C[_]](b: Braided.Aux[->, P, C]): Braided.Aux[Opp[->]#l, P, C] =
    new OppBraided[->, P, C] { val A = b }

  given dualBraided[->[_,_], P[_,_], C[_]](using b: Braided.Aux[->, P, C]): Braided.Aux[Dual[->, *, *], P, C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Braided.Aux[f, P, C]](oppBraided(b))
}

trait DualAssociativeInstances03 {
  def oppAssociative[->[_,_], P[_,_], C[_]](a: Associative.Aux[->, P, C]): Associative.Aux[Opp[->]#l, P, C] =
    new OppAssociative[->, P, C] { val A = a }

  given dualAssociative[->[_,_], P[_,_], C[_]](using a: Associative.Aux[->, P, C]): Associative.Aux[Dual[->, *, *], P, C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Associative.Aux[f, P, C]](oppAssociative(a))
}

trait DualBifunctorInstances {
  def oppEndobifunctor[->[_,_], P[_,_]](e: Endobifunctor[->, P]): Endobifunctor[Opp[->]#l, P] =
    new OppBifunctor[->, P] {val E = e}
  implicit def dualEndobifunctor[->[_,_], P[_,_]](implicit e: Endobifunctor[->, P]): Endobifunctor[Dual[->,*,*], P] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Endobifunctor[f, P]](oppEndobifunctor(e))
}

object DualHelpers {
  trait OppSemicategory[->[_,_]] extends Semicategory[Opp[->]#l] {
    protected def S: Semicategory[->]
    override def andThen[X, Y, Z](ab: Y -> X, bc: Z -> Y): Z -> X = S.andThen(bc, ab)
  }

  trait OppSubcat[->[_,_], C[_]] extends OppSemicategory[->] with Subcat[Opp[->]#l] {
    type TC[a] = C[a]
    protected def S: Subcat.Aux[->, C]
    override def id[A](using A: TC[A]): A -> A = S.id[A]
  }

  trait OppBifunctor[->[_,_], ⊙[_,_]] extends Endobifunctor[Opp[->]#l, ⊙] {
    protected def E: Endobifunctor[->, ⊙]
    override def bimap[A, X, B, Y](left: X -> A, right: Y -> B): ⊙[X, Y] -> ⊙[A, B] = E.bimap(left, right)
  }

  trait OppAssociative[->[_,_], ⊙[_,_], C[_]] extends Associative[Opp[->]#l, ⊙] {
    protected def A: Associative.Aux[->, ⊙, C]
    type TC[a] = C[a]
    def C = Dual.oppSubcat(A.C)
    def bifunctor = Dual.oppEndobifunctor(A.bifunctor)
    def associate  [X: TC, Y: TC, Z: TC]: (X ⊙ (Y ⊙ Z)) -> (X ⊙ Y ⊙ Z) = A.diassociate
    def diassociate[X: TC, Y: TC, Z: TC]: (X ⊙ Y ⊙ Z) -> (X ⊙ (Y ⊙ Z)) = A.associate
  }

  trait OppBraided[->[_,_], ⊙[_,_], C[_]] extends OppAssociative[->, ⊙, C] with Braided[Opp[->]#l, ⊙] {
    protected def A: Braided.Aux[->, ⊙, C]
    def braid[A: C, B: C]: (B ⊙ A) -> (A ⊙ B) = A.braid
  }

  trait OppMonoidal[->[_,_], ⊙[_,_], C[_], I] extends OppAssociative[->, ⊙, C] with Monoidal[Opp[->]#l, ⊙] {
    type Id = I
    protected def A: Monoidal.Aux[->, ⊙, C, I]
    def idl  [A: C]: A -> ⊙[I, A] = A.coidl
    def coidl[A: C]: ⊙[I, A] -> A = A.idl
    def idr  [A: C]: A -> ⊙[A, I] = A.coidr
    def coidr[A: C]: ⊙[A, I] -> A = A.idr
  }
}
