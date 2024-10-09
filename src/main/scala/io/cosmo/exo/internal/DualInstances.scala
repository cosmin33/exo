package io.cosmo.exo.internal

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.functors.*

trait DualInstances extends DualAssociativeInstances
  with DualSemicategoryInstances
  with DualBifunctorInstances
  
import DualHelpers._
trait DualSemicategoryInstances extends DualSemicategoryInstances01 {
  given oppSubcat[->[_,_], C[_]](using s: Subcat.Aux[->, C]): Subcat.Aux[Opp[->], C] =
    new OppSubcat[->, C] { val underlying = s }

  given dualSubcat[->[_,_], C[_]](using s: Subcat.Aux[->, C]): Subcat.Aux[Dual[->, *, *], C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Subcat.Aux[f, C]](oppSubcat(using s))

  given dualdualSubcat[->[_, _], T[_]](using Subcat.Aux[Dual[->, *, *], T]): Subcat.Aux[->, T] =
    Dual.nestedDualCancelsItself.subst[[f[_, _]] =>> Subcat.Aux[f, T]](dualSubcat)
}

trait DualSemicategoryInstances01 {
  given oppSemicat[->[_,_]](using s: Semicategory[->]): Semicategory[Opp[->]] =
    new OppSemicategory[->] { val underlying = s }

  given dualSemicat[->[_,_]](using s: Semicategory[->]): Semicategory[Dual[->, *, *]] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Semicategory[f]](oppSemicat(using s))

  given dualdualSemicat[->[_, _], T[_]](using Semicategory[Dual[->, *, *]]): Semicategory[->] =
    Dual.nestedDualCancelsItself.subst[[f[_, _]] =>> Semicategory[f]](dualSemicat)
}

trait DualAssociativeInstances extends DualAssociativeInstances01 {
  given oppMonoidal[->[_,_], P[_,_], C[_], I](using m: Monoidal.Aux[->, P, C, I]): Monoidal.Aux[Opp[->], P, C, I] =
    new OppMonoidal[->, P, C, I] { val underlying = m }

  given dualMonoidal[->[_,_], P[_,_], C[_], I](using m: Monoidal.Aux[->, P, C, I]): Monoidal.Aux[Dual[->, *, *], P, C, I] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Monoidal.Aux[f, P, C, I]](oppMonoidal(using m))

  given dualdualMonoidal[->[_, _], ⊙[_, _], T[_], I](using Monoidal.Aux[Dual[->, *, *], ⊙, T, I]): Monoidal.Aux[->, ⊙, T, I] =
    Dual.nestedDualCancelsItself.subst[[f[_, _]] =>> Monoidal.Aux[f, ⊙, T, I]](dualMonoidal)
}

trait DualAssociativeInstances01 extends DualAssociativeInstances02 {
  given oppSymmetric[->[_,_], P[_,_], C[_]](using s: Symmetric.Aux[->, P, C]): Symmetric.Aux[Opp[->], P, C] =
    new Symmetric[Opp[->], P] with OppBraided[->, P, C] { val underlying = s }

  given dualSymmetric[->[_,_], P[_,_], C[_]](using s: Symmetric.Aux[->, P, C]): Symmetric.Aux[Dual[->, *, *], P, C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Symmetric.Aux[f, P, C]](oppSymmetric(using s))

  given dualdualSymmetric[->[_, _], ⊙[_, _], T[_]](using Symmetric.Aux[Dual[->, *, *], ⊙, T]): Symmetric.Aux[->, ⊙, T] =
    Dual.nestedDualCancelsItself.subst[[f[_, _]] =>> Symmetric.Aux[f, ⊙, T]](dualSymmetric)
}

trait DualAssociativeInstances02 extends DualAssociativeInstances03 {
  given oppBraided[->[_,_], P[_,_], C[_]](using b: Braided.Aux[->, P, C]): Braided.Aux[Opp[->], P, C] =
    new OppBraided[->, P, C] { val underlying = b }

  given dualBraided[->[_,_], P[_,_], C[_]](using b: Braided.Aux[->, P, C]): Braided.Aux[Dual[->, *, *], P, C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Braided.Aux[f, P, C]](oppBraided(using b))

  given dualdualBraided[->[_, _], ⊙[_, _], T[_]](using Braided.Aux[Dual[->, *, *], ⊙, T]): Braided.Aux[->, ⊙, T] =
    Dual.nestedDualCancelsItself.subst[[f[_, _]] =>> Braided.Aux[f, ⊙, T]](dualBraided)
}

trait DualAssociativeInstances03 {
  given oppAssociative[->[_,_], P[_,_], C[_]](using a: Associative.Aux[->, P, C]): Associative.Aux[Opp[->], P, C] =
    new OppAssociative[->, P, C] { val underlying = a }

  given dualAssociative[->[_,_], P[_,_], C[_]](using a: Associative.Aux[->, P, C]): Associative.Aux[Dual[->, *, *], P, C] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Associative.Aux[f, P, C]](oppAssociative(using a))

  given dualdualAssociative[->[_, _], ⊙[_, _], T[_]](using Associative.Aux[Dual[->, *, *], ⊙, T]): Associative.Aux[->, ⊙, T] =
    Dual.nestedDualCancelsItself.subst[[f[_, _]] =>> Associative.Aux[f, ⊙, T]](dualAssociative)
}

trait DualBifunctorInstances extends DualBifunctorInstances01 {
  given oppEndobifunctor[->[_,_], P[_,_]](using e: Endobifunctor[->, P]): Endobifunctor[Opp[->], P] =
    new OppBifunctor[->, P] {val underlying = e}

  given dualEndobifunctor[->[_,_], P[_,_]](using e: Endobifunctor[->, P]): Endobifunctor[Dual[->,*,*], P] =
    Dual.leibniz[->].subst[[f[_,_]] =>> Endobifunctor[f, P]](oppEndobifunctor(using e))

  // if this is a "given" then I have strange errors about implicits found in more than one place
  def dualdualEndobifunctor[->[_, _], ⊙[_, _]](using Endobifunctor[Dual[->, *, *], ⊙]): Endobifunctor[->, ⊙] =
    Dual.nestedDualCancelsItself.subst[[f[_, _]] =>> Endobifunctor[f, ⊙]](Exobifunctor.dualEndobifunctor)
}

trait DualBifunctorInstances01 {
}

object DualHelpers {
  trait OppSemicategory[->[_,_]] extends Semicategory[Opp[->]]:
    protected def underlying: Semicategory[->]
    override def andThen[X, Y, Z](ab: Y -> X, bc: Z -> Y): Z -> X = underlying.andThen(bc, ab)

  trait OppSubcat[->[_,_], C[_]] extends OppSemicategory[->] with Subcat[Opp[->]]:
    type TC[a] = C[a]
    protected def underlying: Subcat.Aux[->, C]
    override def id[A](using A: TC[A]): A -> A = underlying.id[A]

  trait OppBifunctor[->[_,_], ⊙[_,_]] extends Endobifunctor[Opp[->], ⊙]:
    protected def underlying: Endobifunctor[->, ⊙]
    override def bimap[A, X, B, Y](left: X -> A, right: Y -> B): ⊙[X, Y] -> ⊙[A, B] = underlying.bimap(left, right)

  trait OppAssociative[->[_,_], ⊙[_,_], C[_]] extends Associative[Opp[->], ⊙]:
    protected def underlying: Associative.Aux[->, ⊙, C]
    type TC[a] = C[a]
    def C = Semicategory.oppSubcat(using underlying.C)
    def bifunctor = Exobifunctor.oppEndobifunctor(using underlying.bifunctor)
    def associate  [X: TC, Y: TC, Z: TC]: (X ⊙ (Y ⊙ Z)) -> (X ⊙ Y ⊙ Z) = underlying.diassociate
    def diassociate[X: TC, Y: TC, Z: TC]: (X ⊙ Y ⊙ Z) -> (X ⊙ (Y ⊙ Z)) = underlying.associate

  trait OppBraided[->[_,_], ⊙[_,_], C[_]] extends OppAssociative[->, ⊙, C] with Braided[Opp[->], ⊙]:
    protected def underlying: Braided.Aux[->, ⊙, C]
    def braid[A: C, B: C]: (B ⊙ A) -> (A ⊙ B) = underlying.braid

  trait OppMonoidal[->[_,_], ⊙[_,_], C[_], I] extends OppAssociative[->, ⊙, C] with Monoidal[Opp[->], ⊙]:
    type Id = I
    protected def underlying: Monoidal.Aux[->, ⊙, C, I]
    def idl  [A: C]: A -> ⊙[I, A] = underlying.coidl
    def coidl[A: C]: ⊙[I, A] -> A = underlying.idl
    def idr  [A: C]: A -> ⊙[A, I] = underlying.coidr
    def coidr[A: C]: ⊙[A, I] -> A = underlying.idr
}
