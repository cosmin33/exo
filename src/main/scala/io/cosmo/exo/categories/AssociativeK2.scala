package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

trait AssociativeK2[->[_,_], ⊙[_,_]]:
  type TC[_[_,_]]
  def C: SubcategoryK2.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [F[_,_]: TC, G[_,_]: TC, H[_,_]: TC]: ∀∀[[a, b] =>> ⊙[⊙[F[a, b], G[a, b]], H[a, b]] -> ⊙[F[a, b], ⊙[G[a, b], H[a, b]]]]
  def diassociate[F[_,_]: TC, G[_,_]: TC, H[_,_]: TC]: ∀∀[[a, b] =>> ⊙[F[a, b], ⊙[G[a, b], H[a, b]]] -> ⊙[⊙[F[a, b], G[a, b]], H[a, b]]]

  def grouped[A[_,_], B[_,_], X[_,_], Y[_,_]](f: ∀∀[[a, b] =>> A[a, b] -> B[a, b]], g: ∀∀[[a, b] =>> X[a, b] -> Y[a, b]]): ∀∀[[a, b] =>> ⊙[A[a, b], X[a, b]] -> ⊙[B[a, b], Y[a, b]]] =
    ∀∀.of[[a, b] =>> ⊙[A[a, b], X[a, b]] -> ⊙[B[a, b], Y[a, b]]](bifunctor.bimap(f.apply, g.apply))

  def strongFirst [F[_,_], G[_,_], H[_,_]: TC](fa: ∀∀[[a, b] =>> F[a, b] -> G[a, b]]): ∀∀[[a, b] =>> ⊙[H[a, b], F[a, b]] -> ⊙[H[a, b], G[a, b]]] = grouped(C.id[H], fa)
  def strongSecond[F[_,_], G[_,_], H[_,_]: TC](fa: ∀∀[[a, b] =>> F[a, b] -> G[a, b]]): ∀∀[[a, b] =>> ⊙[F[a, b], H[a, b]] -> ⊙[G[a, b], H[a, b]]] = grouped(fa, C.id[H])

  private type <->[a[_,_], b[_,_]] = IsoK2[->, a, b]
  def isoAssociator[F[_,_]: TC, G[_,_]: TC, H[_,_]: TC]: ([a,b] =>> ⊙[⊙[F[a,b], G[a,b]], H[a,b]]) <-> ([a,b] =>> ⊙[F[a,b], ⊙[G[a,b], H[a,b]]]) =
    IsoK2.unsafe[->, [a,b] =>> ⊙[⊙[F[a,b], G[a,b]], H[a,b]], [a,b] =>> ⊙[F[a,b], ⊙[G[a,b], H[a,b]]]](associate[F,G,H], diassociate[F,G,H])(using C)

object AssociativeK2 extends AssociativeK2Instances:
  type Aux[->[_,_], ⊙[_,_], TC0[_[_,_]]] = AssociativeK2[->, ⊙] { type TC[A[_,_]] = TC0[A] }
  def apply[->[_,_], ⊙[_,_]](using ev: AssociativeK2[->, ⊙]): AssociativeK2[->, ⊙] = ev
end AssociativeK2

import AssociativeK2InstancesHelpers.*

trait AssociativeK2Instances extends AssociativeK2Instances01:
  given cccK2Upper[->[_,_], ⊙[_,_], |->[_,_], T[_], I](using c: Ccc.Aux[->, ⊙, |->, T, I]): CccK2.Aux[->, ⊙, |->, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]], [a,b] =>> I] =
    new CccK2Upper[->, ⊙, |->, T, I] { val assoc = c }

trait AssociativeK2Instances01 extends AssociativeK2Instances02:
  given cartesianK2Upper[->[_,_], ⊙[_,_], T[_], I](using c: Cartesian.Aux[->, ⊙, T, I]): CartesianK2.Aux[->, ⊙, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]], [a,b] =>> I] =
    new CartesianK2Upper[->, ⊙, T, I] { val assoc = c }

trait AssociativeK2Instances02 extends AssociativeK2Instances03:
  given monoidalK2Upper[->[_,_], ⊙[_,_], T[_], I](using m: Monoidal.Aux[->, ⊙, T, I]): MonoidalK2.Aux[->, ⊙, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]], [a,b] =>> I] =
    new MonoidalK2Upper[->, ⊙, T, I] { val assoc = m }

trait AssociativeK2Instances03 extends AssociativeK2Instances04:
  given symmetricK2Upper[->[_,_], ⊙[_,_], T[_]](using s: Symmetric.Aux[->, ⊙, T]): SymmetricK2.Aux[->, ⊙, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]]] =
    new SymmetricK2Upper[->, ⊙, T] { val assoc = s }

trait AssociativeK2Instances04 extends AssociativeK2Instances05:
  given braidedK2Upper[->[_,_], ⊙[_,_], T[_]](using b: Braided.Aux[->, ⊙, T]): BraidedK2.Aux[->, ⊙, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]]] =
    new BraidedK2Upper[->, ⊙, T] { val assoc = b }

trait AssociativeK2Instances05:
  given associativeK2Upper[->[_,_], ⊙[_,_], T[_]](using a: Associative.Aux[->, ⊙, T]): AssociativeK2.Aux[->, ⊙, [f[_,_]] =>> ∀∀[[a, b] =>> T[f[a, b]]]] =
    new AssociativeK2Upper[->, ⊙, T] { val assoc = a }

private object AssociativeK2InstancesHelpers:
  trait AssociativeK2Upper[->[_,_], ⊙[_,_], T[_]] extends AssociativeK2[->, ⊙]:
    type TC[f[_,_]] = ∀∀[[a, b] =>> T[f[a, b]]]
    protected def assoc: Associative.Aux[->, ⊙, T]
    def C: SubcategoryK2.Aux[->, TC] = SemicategoryK2.subcatK2Upper[->, T](using assoc.C)
    def bifunctor: Endobifunctor[->, ⊙] = assoc.bifunctor
    def associate  [F[_,_], G[_,_], H[_,_]](using F: TC[F], G: TC[G], H: TC[H]): ∀∀[[a, b] =>> ⊙[⊙[F[a, b], G[a, b]], H[a, b]] -> ⊙[F[a, b], ⊙[G[a, b], H[a, b]]]] =
      ∀∀[[a, b] =>> ⊙[⊙[F[a, b], G[a, b]], H[a, b]] -> ⊙[F[a, b], ⊙[G[a, b], H[a, b]]]](assoc.associate(using F.apply, G.apply, H.apply))
    def diassociate[F[_,_], G[_,_], H[_,_]](using F: TC[F], G: TC[G], H: TC[H]): ∀∀[[a, b] =>> ⊙[F[a, b], ⊙[G[a, b], H[a, b]]] -> ⊙[⊙[F[a, b], G[a, b]], H[a, b]]] =
      ∀∀[[a, b] =>> ⊙[F[a, b], ⊙[G[a, b], H[a, b]]] -> ⊙[⊙[F[a, b], G[a, b]], H[a, b]]](assoc.diassociate(using F.apply, G.apply, H.apply))
  trait MonoidalK2Upper[->[_,_], ⊙[_,_], T[_], I] extends AssociativeK2Upper[->, ⊙, T] with MonoidalK2[->, ⊙]:
    type Id[a, b] = I
    protected def assoc: Monoidal.Aux[->, ⊙, T, I]
    def idl  [F[_,_]: TC]: ∀∀[[a, b] =>> ⊙[Id[a, b], F[a, b]] -> F[a, b]] = ∀∀[[a, b] =>> ⊙[Id[a, b], F[a, b]] -> F[a, b]](assoc.idl(using summon[TC[F]].apply))
    def coidl[F[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] -> (I ⊙ F[a, b])] =        ∀∀[[a, b] =>> F[a, b] -> (I ⊙ F[a, b])](assoc.coidl(using summon[TC[F]].apply))
    def idr  [F[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] ⊙ I -> F[a, b]] =          ∀∀[[a, b] =>> F[a, b] ⊙ I -> F[a, b]](assoc.idr(using summon[TC[F]].apply))
    def coidr[F[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] -> (F[a, b] ⊙ I)] =        ∀∀[[a, b] =>> F[a, b] -> (F[a, b] ⊙ I)](assoc.coidr(using summon[TC[F]].apply))
  trait BraidedK2Upper[->[_,_], ⊙[_,_], T[_]] extends AssociativeK2Upper[->, ⊙, T] with BraidedK2[->, ⊙]:
    protected def assoc: Braided.Aux[->, ⊙, T]
    def braid[A[_,_]: TC, B[_,_]: TC]: ∀∀[[a, b] =>> ⊙[A[a, b], B[a, b]] -> ⊙[B[a, b], A[a, b]]] =
      ∀∀[[a, b] =>> ⊙[A[a, b], B[a, b]] -> ⊙[B[a, b], A[a, b]]](assoc.braid(using summon[TC[A]].apply, summon[TC[B]].apply))
  trait SymmetricK2Upper[->[_,_], ⊙[_,_], T[_]] extends BraidedK2Upper[->, ⊙, T] with SymmetricK2[->, ⊙]:
    protected def assoc: Symmetric.Aux[->, ⊙, T]
  trait CartesianK2Upper[->[_,_], ⊙[_,_], T[_], I] extends MonoidalK2Upper[->, ⊙, T, I] with SymmetricK2Upper[->, ⊙, T] with CartesianK2[->, ⊙]:
    protected def assoc: Cartesian.Aux[->, ⊙, T, I]
    def fst[F[_,_]: TC, G[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] ⊙ G[a, b] -> F[a, b]] = ∀∀[[a, b] =>> F[a, b] ⊙ G[a, b] -> F[a, b]](assoc.fst(using summon[TC[F]].apply, summon[TC[G]].apply))
    def snd[F[_,_]: TC, G[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] ⊙ G[a, b] -> G[a, b]] = ∀∀[[a, b] =>> F[a, b] ⊙ G[a, b] -> G[a, b]](assoc.snd(using summon[TC[F]].apply, summon[TC[G]].apply))
    def diag[F[_,_]: TC]: ∀∀[[a, b] =>> F[a, b] -> (F[a, b] ⊙ F[a, b])] = ∀∀[[a, b] =>> F[a, b] -> (F[a, b] ⊙ F[a, b])](assoc.diag(using summon[TC[F]].apply))
    def &&&[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], g: ∀∀[[a, b] =>> F[a, b] -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> (G[a, b] ⊙ H[a, b])] =
      ∀∀[[a, b] =>> F[a, b] -> (G[a, b] ⊙ H[a, b])](assoc.&&&(f.apply, g.apply))
  trait CccK2Upper[->[_,_], ⊙[_,_], |->[_,_], T[_], I] extends CartesianK2Upper[->, ⊙, T, I] with CccK2[->, ⊙, |->]:
    protected def assoc: Ccc.Aux[->, ⊙, |->, T, I]
    def curry  [F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> (F[a, b] ⊙ G[a, b]) -> H[a, b]]): ∀∀[[a, b] =>> F[a, b] -> (G[a, b] |-> H[a, b])] =
      ∀∀[[a, b] =>> F[a, b] -> (G[a, b] |-> H[a, b])](assoc.curry(f.apply))
    def uncurry[F[_,_], G[_,_], H[_,_]](f: ∀∀[[a, b] =>> F[a, b] -> (G[a, b] |-> H[a, b])]): ∀∀[[a, b] =>> (F[a, b] ⊙ G[a, b]) -> H[a, b]] =
      ∀∀[[a, b] =>> (F[a, b] ⊙ G[a, b]) -> H[a, b]](assoc.uncurry(f.apply))
end AssociativeK2InstancesHelpers
