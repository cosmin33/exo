package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.*

trait Semicategory[->[_,_]]:
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C

object Semicategory
  extends SemicategoryImplicits
  with Function1SemicategoryInstances
  with DualSemicategoryInstances
  with EvidenceCatSubcatInstances
  with ProdcatSemicategoryInstances:
  
  def apply[->[_,_]](using ev: Semicategory[->]): Semicategory[->] = ev

end Semicategory

import SemicategoryHelpers.*

trait SemicategoryImplicits extends SemicategoryImplicits01:
  given distributiveArrowFunctor[->[_,_], T[_], P[_,_], PI, S[_,_], SI]
  : IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Distributive.Aux[f, T, P, PI, S, SI]] =
    new IsoFunctorK2.ProtoF[[f[_,_]] =>> Distributive.Aux[f, T, P, PI, S, SI]]:
      protected def mapK2[==>[_,_], -->[_,_]](iso: ==> <~~> -->)
      : Distributive.Aux[==>, T, P, PI, S, SI] => Distributive.Aux[-->, T, P, PI, S, SI] =
        s1 => new DistributiveArrowFunctor[==>, -->, T, P, PI, S, SI] { val I = iso; val S = s1 }
  given distributiveTypeclassFunctor[->[_,_], T0[_], T[_], P[_,_], PI, S[_,_], SI]
  : CofunctorK[* => *, * => *, [f[_]] =>> Distributive.Aux[->, f, P, PI, S, SI]] =
    new CofunctorK.ProtoF[[f[_]] =>> Distributive.Aux[->, f, P, PI, S, SI]]:
      override protected def comapK[F[_], G[_]](f: G ~> F)
      : Distributive.Aux[->, F, P, PI, S, SI] => Distributive.Aux[->, G, P, PI, S, SI] =
        s1 => new DistributiveTypeclassFunctor[->, F, G, P, PI, S, SI] { val fk = f; val S = s1 }

trait SemicategoryImplicits01 extends SemicategoryImplicits02:
  given concreteArrowFunctor[->[_,_], T[_]]: IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Concrete.Aux[f, T]] =
    new IsoFunctorK2.ProtoF[[f[_,_]] =>> Concrete.Aux[f, T]]:
      protected def mapK2[==>[_,_], -->[_,_]](iso: ==> <~~> -->): Concrete.Aux[==>, T] => Concrete.Aux[-->, T] =
        s1 => new ConcreteArrowFunctor[==>, -->, T] { val I = iso; val S = s1 }
  given concreteTypeclassFunctor[->[_,_], T0[_], T[_]]: IsoFunctorK[* => *, * => *, [f[_]] =>> Concrete.Aux[->, f]] =
    new IsoFunctorK.ProtoF[[f[_]] =>> Concrete.Aux[->, f]]:
      override protected def mapK[F[_], G[_]](f: F <~> G): Concrete.Aux[->, F] => Concrete.Aux[->, G] =
        s1 => new ConcreteTypeclassFunctor[->, F, G] { val I = f.flip; val S = s1 }

trait SemicategoryImplicits02 extends SemicategoryImplicits03:
  given subcatArrowFunctor[->[_,_], T[_]]: IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Subcat.Aux[f, T]] =
    new IsoFunctorK2.ProtoF[[f[_,_]] =>> Subcat.Aux[f, T]]:
      protected def mapK2[==>[_,_], -->[_,_]](iso: ==> <~~> -->): Subcat.Aux[==>, T] => Subcat.Aux[-->, T] =
        s1 => new SubcatArrowFunctor[==>, -->, T] { val I = iso; val S = s1 }
  given subcatTypeclassFunctor[->[_,_], T0[_], T[_]]: CofunctorK[* => *, * => *, [f[_]] =>> Subcat.Aux[->, f]] =
    new CofunctorK.Proto1[* => *, [f[_]] =>> Subcat.Aux[->, f]]:
      override protected def comapK[F[_], G[_]](f: G ~> F): Subcat.Aux[->, F] => Subcat.Aux[->, G] =
        s1 => new SubcatTypeclassFunctor[->, F, G] { val fk = f; val S = s1 }

trait SemicategoryImplicits03:
  given semicatArrowFunctor[->[_,_]]: IsoFunctorK2[* => *, * => *, Semicategory] =
    new IsoFunctorK2.ProtoF[[f[_,_]] =>> Semicategory[f]]:
      protected def mapK2[==>[_,_], -->[_,_]](iso: ==> <~~> -->): Semicategory[==>] => Semicategory[-->] =
        s1 => new SemicatArrowFunctor[==>, -->] { val I = iso; val S = s1 }

object SemicategoryHelpers:
  trait SemicatArrowFunctor[==>[_,_], -->[_,_]] extends Semicategory[-->]:
    protected def I: ==> <~~> -->
    protected def S: Semicategory[==>]
    def andThen[A, B, C](ab: A --> B, bc: B --> C): A --> C = I.to(S.andThen(I.from(ab), I.from(bc)))

  trait SubcatArrowFunctor[==>[_,_], -->[_,_], T[_]] extends SemicatArrowFunctor[==>, -->] with Subcategory[-->]:
    type TC[a] = T[a]
    protected def S: Subcategory.Aux[==>, T]
    def id[A: T]: -->[A, A] = I[A, A](S.id[A])

  trait ConcreteArrowFunctor[==>[_,_], -->[_,_], T[_]] extends SubcatArrowFunctor[==>, -->, T] with Concrete[-->]:
    protected def S: Concrete.Aux[==>, T]
    def concretize[A, B](f: A --> B): (A, T[A]) => (B, T[B]) = S.concretize(I.from(f))

  trait DistributiveArrowFunctor[==>[_,_], -->[_,_], T[_], ⨂[_,_], PI, ⨁[_,_], SI]
    extends SubcatArrowFunctor[==>, -->, T] with Distributive[-->, ⨂, ⨁]:
    type ProductId = PI
    type SumId = SI
    protected def S: Distributive.Aux[==>, T, ⨂, PI, ⨁, SI]
    def cartesian: Cartesian.Aux[--> , ⨂, T, PI] = ???
    def cocartesian: Cocartesian.Aux[--> , ⨁, T, SI] = ???
    override def distribute  [A: T, B: T, C: T]: ⨂[A, ⨁[B, C]] --> ⨁[⨂[A, B], ⨂[A, C]] = I.to(S.distribute)
    override def codistribute[A: T, B: T, C: T]: ⨁[⨂[A, B], ⨂[A, C]] --> ⨂[A, ⨁[B, C]] = I.to(S.codistribute)

  trait SubcatTypeclassFunctor[->[_,_], T0[_], T[_]] extends Subcategory[->]:
    protected def fk: T ~> T0
    protected def S: Subcategory.Aux[->, T0]
    type TC[a] = T[a]
    def id[A](using T: T[A]): A -> A = S.id[A](using fk[A](T))
    def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C = S.andThen(ab, bc)

  trait ConcreteTypeclassFunctor[->[_,_], T0[_], T[_]] extends SubcatTypeclassFunctor[->, T0, T] with Concrete[->]:
    type TC[a] = T[a]
    protected def I: T <~> T0
    override def fk: T ~> T0 = I.to
    override def S: Concrete.Aux[->, T0]
    def concretize[A, B](f: A -> B): (A, T[A]) => (B, T[B]) =
      case (a, ta) =>
        val (b, tb) = S.concretize(f)(a, I.to(ta))
        (b, I.from(tb))

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

end SemicategoryHelpers
