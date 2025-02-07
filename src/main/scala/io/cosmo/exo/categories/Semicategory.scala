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

trait SemicategoryImplicits:
  // functors on the arrow type parameter
  given semicatArrowFunctor: IsofunctorK2[Semicategory] =
    new IsofunctorK2.Proto[Semicategory]:
      override def isomap[==>[_,_], -->[_,_]](i: ==> <~~> -->): Semicategory[==>] => Semicategory[-->] =
        s => new SemicatArrowFunctor[==>, -->] { val I = i; val S = s }
  given subcatArrowFunctor[T[_]]: IsofunctorK2[[f[_,_]] =>> Subcat.Aux[f, T]] =
    new IsofunctorK2.Proto[[f[_,_]] =>> Subcat.Aux[f, T]]:
      override def isomap[==>[_,_], -->[_,_]](i: ==> <~~> -->): Subcat.Aux[==>, T] => Subcat.Aux[-->, T] =
        s => new SubcatArrowFunctor[==>, -->, T] { val I = i; val S = s }
  given concreteArrowFunctor[T[_]]: IsofunctorK2[[f[_,_]] =>> Concrete.Aux[f, T]] =
    new IsofunctorK2.Proto[[f[_,_]] =>> Concrete.Aux[f, T]]:
      override def isomap[==>[_,_], -->[_,_]](i: ==> <~~> -->): Concrete.Aux[==>, T] => Concrete.Aux[-->, T] =
        s => new ConcreteArrowFunctor[==>, -->, T] { val I = i; val S = s }
  given distributiveArrowFunctor[T[_], ⨂[_,_], PI, ⨁[_,_], SI]: IsofunctorK2[[f[_,_]] =>> Distributive.Aux[f, T, ⨂, PI, ⨁, SI]] =
    new IsofunctorK2.Proto[[f[_,_]] =>> Distributive.Aux[f, T, ⨂, PI, ⨁, SI]]:
      override def isomap[==>[_,_], -->[_,_]](i: ==> <~~> -->): Distributive.Aux[==>, T, ⨂, PI, ⨁, SI] => Distributive.Aux[-->, T, ⨂, PI, ⨁, SI] =
        s => new DistributiveArrowFunctor[==>, -->, T, ⨂, PI, ⨁, SI] { val I = i; val S = s }

  // functors on the typeclass type parameter
  given subcatTypeclassFunctor[->[_,_]]: ContravariantK[[t[_]] =>> Subcat.Aux[->, t]] =
    new ContravariantK.Proto[[t[_]] =>> Subcat.Aux[->, t]]:
      override def comap[F[_], G[_]](f: G ~> F): Subcat.Aux[->, F] => Subcat.Aux[->, G] =
        s => new SubcatTypeclassFunctor[->, F, G] { val fk = f; val S = s }
  given concreteTypeclassFunctor[->[_,_]]: IsofunctorK[[t[_]] =>> Concrete.Aux[->, t]] =
    new IsofunctorK.Proto[[t[_]] =>> Concrete.Aux[->, t]]:
      def isomap[F[_], G[_]](i: F <~> G): Concrete.Aux[->, F] => Concrete.Aux[->, G] =
        s => new ConcreteTypeclassFunctor[->, F, G] { val I = i; val S = s }
  given distributiveTypeclassFunctor[->[_,_], P[_,_], PI, S[_,_], SI]: ContravariantK[[t[_]] =>> Distributive.Aux[->, t, P, PI, S, SI]] =
    new ContravariantK.Proto[[t[_]] =>> Distributive.Aux[->, t, P, PI, S, SI]]:
      override def comap[F[_], G[_]](f: G ~> F): Distributive.Aux[->, F, P, PI, S, SI] => Distributive.Aux[->, G, P, PI, S, SI] =
        s => new DistributiveTypeclassFunctor[->, F, G, P, PI, S, SI] { val fk = f; val S = s }
end SemicategoryImplicits

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

  trait SubcatTypeclassFunctor[->[_,_], T[_], T0[_]] extends Subcategory[->]:
    protected def fk: T0 ~> T
    protected def S: Subcategory.Aux[->, T]
    type TC[a] = T0[a]
    def id[A](using T: T0[A]): A -> A = S.id[A](using fk[A](T))
    def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C = S.andThen(ab, bc)

  trait ConcreteTypeclassFunctor[->[_,_], T[_], T0[_]] extends SubcatTypeclassFunctor[->, T, T0] with Concrete[->]:
    type TC[a] = T0[a]
    protected def I: T <~> T0
    override def fk: T0 ~> T = I.fromK
    override def S: Concrete.Aux[->, T]
    def concretize[A, B](f: A -> B): (A, T0[A]) => (B, T0[B]) =
      case (a, ta) =>
        val (b, tb) = S.concretize(f)(a, I.apply.from(ta))
        (b, I.apply.to(tb))

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
