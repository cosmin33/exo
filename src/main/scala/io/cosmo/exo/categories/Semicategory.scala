package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.*

trait Semicategory[->[_,_]]:
  self =>
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)

  def semicatK: SemicategoryK[->] = new SemicategoryK[->]:
    def andThen[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> G[a] -> H[a]]): ∀[[a] =>> F[a] -> H[a]] =
      ∀[[a] =>> F[a] -> H[a]](self.andThen(f.apply, g.apply))
  def semicatK2: SemicategoryK2[->] = new SemicategoryK2[->]:
    def andThen[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a,b] =>> F[a,b] -> G[a,b]], g: ∀∀[[a,b] =>> G[a,b] -> H[a,b]]): ∀∀[[a,b] =>> F[a,b] -> H[a,b]] =
      ∀∀[[a,b] =>> F[a,b] -> H[a,b]](self.andThen(f.apply, g.apply))
  def semicatH: SemicategoryH[->] = new SemicategoryH[->]:
    def andThen[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]], g: ∀~[[a[_]] =>> G[a] -> H[a]]): ∀~[[a[_]] =>> F[a] -> H[a]] =
      ∀~[[a[_]] =>> F[a] -> H[a]](self.andThen(f.apply, g.apply))

object Semicategory
  extends SemicategoryImplicits
  with Function1SemicategoryInstances
  with DualSemicategoryInstances
  with EvidenceCatSubcatInstances
  with ProdcatSemicategoryInstances:
  
  def apply[->[_,_]](using ev: Semicategory[->]): Semicategory[->] = ev

end Semicategory

import SemicategoryImplicitsHelpers.*

trait SemicategoryImplicits {
  
}

object SemicategoryImplicitsHelpers:
  trait SemicatArrowFunctor[==>[_,_], -->[_,_]] extends Semicategory[-->]:
    protected def I: ==> <~~> -->
    protected def S: Semicategory[==>]
    def andThen[A, B, C](ab: A --> B, bc: B --> C): A --> C = I.apply.to(S.andThen(I.apply.from(ab), I.apply.from(bc)))

  trait SubcatArrowFunctor[==>[_,_], -->[_,_], T[_]] extends SemicatArrowFunctor[==>, -->] with Subcategory[-->]:
    type TC[a] = T[a]
    protected def S: Subcategory.Aux[==>, T]
    def id[A: T]: -->[A, A] = I.apply[A, A].to(S.id[A])

  trait ConcreteArrowFunctor[==>[_,_], -->[_,_], T[_]] extends SubcatArrowFunctor[==>, -->, T] with Concrete[-->]:
    protected def S: Concrete.Aux[==>, T]
    def concretize[A, B](f: A --> B): (A, T[A]) => (B, T[B]) = S.concretize(I.apply.from(f))

  trait DistributiveArrowFunctor[==>[_,_], -->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI]
    extends SubcatArrowFunctor[==>, -->, T] with Distributive[-->, ⨂, ⨁]:
    type ProductId = PI
    type SumId = SI
    protected def S: Distributive.Aux[==>, T, ⨂, PI, ⨁, SI]
    def cartesian: Cartesian.Aux[--> , ⨂, T, PI] = ???
    def cocartesian: Cocartesian.Aux[--> , ⨁, T, SI] = ???
    override def distribute  [A: T, B: T, C: T]: ⨂[A, ⨁[B, C]] --> ⨁[⨂[A, B], ⨂[A, C]] = I.apply.to(S.distribute)
    override def codistribute[A: T, B: T, C: T]: ⨁[⨂[A, B], ⨂[A, C]] --> ⨂[A, ⨁[B, C]] = I.apply.to(S.codistribute)

  trait SubcatTypeclassFunctor[->[_,_], T0[_], T[_]] extends Subcategory[->]:
    protected def fk: T ~> T0
    protected def S: Subcategory.Aux[->, T0]
    type TC[a] = T[a]
    def id[A](using T: T[A]): A -> A = S.id[A](using fk[A](T))
    def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C = S.andThen(ab, bc)

  trait ConcreteTypeclassFunctor[->[_,_], T0[_], T[_]] extends SubcatTypeclassFunctor[->, T0, T] with Concrete[->]:
    type TC[a] = T[a]
    protected def I: T <~> T0
    override def fk: T ~> T0 = I.toK
    override def S: Concrete.Aux[->, T0]
    def concretize[A, B](f: A -> B): (A, T[A]) => (B, T[B]) =
      case (a, ta) =>
        val (b, tb) = S.concretize(f)(a, I.apply.to(ta))
        (b, I.apply.from(tb))

  trait DistributiveTypeclassFunctor[->[_,_], T0[_], T[_], P[_,_], PI, S[_,_], SI]
    extends SubcatTypeclassFunctor[->, T0, T] with Distributive[->, P, S]:
    type ProductId = PI
    type SumId = SI
    protected def S: Distributive.Aux[->, T0, P, PI, S, SI]
    def cartesian: Cartesian.Aux[->, P, T, PI] = ???
    def cocartesian: Cocartesian.Aux[->, S, T, SI] = ???
    override def distribute  [A, B, C](using ta: T[A], tb: T[B], tc: T[C]): P[A, S[B, C]] -> S[P[A, B], P[A, C]] =
      S.distribute(using fk[A](ta), fk[B](tb), fk[C](tc))
    override def codistribute[A, B, C](using ta: T[A], tb: T[B], tc: T[C]): S[P[A, B], P[A, C]] -> P[A, S[B, C]] =
      S.codistribute(using fk[A](ta), fk[B](tb), fk[C](tc))

end SemicategoryImplicitsHelpers
