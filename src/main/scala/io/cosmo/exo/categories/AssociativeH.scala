package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

trait AssociativeH[->[_,_], ⊙[_,_]]:
  type TC[_[_[_]]]
  def C: SubcategoryH.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [A[_[_]]: TC, B[_[_]]: TC, C[_[_]]: TC]: ∀~[[x[_]] =>> ⊙[⊙[A[x], B[x]], C[x]] -> ⊙[A[x], ⊙[B[x], C[x]]]]
  def diassociate[A[_[_]]: TC, B[_[_]]: TC, C[_[_]]: TC]: ∀~[[x[_]] =>> ⊙[A[x], ⊙[B[x], C[x]]] -> ⊙[⊙[A[x], B[x]], C[x]]]

  def grouped[A[_[_]], B[_[_]], X[_[_]], Y[_[_]]](f: ∀~[[a[_]] =>> A[a] -> B[a]], g: ∀~[[a[_]] =>> X[a] -> Y[a]]): ∀~[[a[_]] =>> ⊙[A[a], X[a]] -> ⊙[B[a], Y[a]]] =
    ∀~.of[[a[_]] =>> ⊙[A[a], X[a]] -> ⊙[B[a], Y[a]]](bifunctor.bimap(f.apply, g.apply))

  def strongFirst [A[_[_]], B[_[_]], C[_[_]]: TC](fa: ∀~[[a[_]] =>> A[a] -> B[a]]): ∀~[[a[_]] =>> ⊙[C[a], A[a]] -> ⊙[C[a], B[a]]] = grouped(C.id[C], fa)
  def strongSecond[A[_[_]], B[_[_]], C[_[_]]: TC](fa: ∀~[[a[_]] =>> A[a] -> B[a]]): ∀~[[a[_]] =>> ⊙[A[a], C[a]] -> ⊙[B[a], C[a]]] = grouped(fa, C.id[C])

  private type <->[a[_[_]], b[_[_]]] = IsoH[->, a, b]
  def isoAssociator[F[_[_]], G[_[_]], H[_[_]]](using F: TC[F], G: TC[G], H: TC[H]): ([a[_]] =>> ⊙[⊙[F[a], G[a]], H[a]]) <-> ([a[_]] =>> ⊙[F[a], ⊙[G[a], H[a]]]) =
    IsoH.unsafe[->, [a[_]] =>> ⊙[⊙[F[a], G[a]], H[a]], [a[_]] =>> ⊙[F[a], ⊙[G[a], H[a]]]](associate[F,G,H], diassociate[F,G,H])(using C)

object AssociativeH:
  type Aux[->[_,_], ⊙[_,_], TC0[_[_[_]]]] = AssociativeH[->, ⊙] { type TC[A[_[_]]] = TC0[A] }
  def apply[->[_,_], ⊙[_,_]](using ev: AssociativeH[->, ⊙]): AssociativeH[->, ⊙] = ev
end AssociativeH

import AssociativeHInstancesHelpers.*

private trait AssociativeHInstances extends AssociativeHInstances01:
  given cccHUpper[->[_,_], ⊙[_,_], |->[_,_], T[_], I](using c: Ccc.Aux[->, ⊙, |->, T, I]): CccH.Aux[->, ⊙, |->, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]], [a[_]] =>> I] =
    new CccHUpper[->, ⊙, |->, T, I] { val assoc = c }
  
private trait AssociativeHInstances01 extends AssociativeHInstances02:
  given cartesianHUpper[->[_,_], ⊙[_,_], T[_], I](using a: Cartesian.Aux[->, ⊙, T, I]): CartesianH.Aux[->, ⊙, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]], [a[_]] =>> I] =
    new CartesianHUpper[->, ⊙, T, I] { val assoc = a }

private trait AssociativeHInstances02 extends AssociativeHInstances03:
  given monoidalHUpper[->[_,_], ⊙[_,_], T[_], I](using a: Monoidal.Aux[->, ⊙, T, I]): MonoidalH.Aux[->, ⊙, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]], [a[_]] =>> I] =
    new MonoidalHUpper[->, ⊙, T, I] { val assoc = a }

private trait AssociativeHInstances03 extends AssociativeHInstances04:
  given symmetricHUpper[->[_,_], ⊙[_,_], T[_]](using a: Symmetric.Aux[->, ⊙, T]): SymmetricH.Aux[->, ⊙, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]]] =
    new SymmetricHUpper[->, ⊙, T] { val assoc = a }

private trait AssociativeHInstances04 extends AssociativeHInstances05:
  given braidedHUpper[->[_,_], ⊙[_,_], T[_]](using a: Braided.Aux[->, ⊙, T]): BraidedH.Aux[->, ⊙, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]]] =
    new BraidedHUpper[->, ⊙, T] { val assoc = a }

private trait AssociativeHInstances05:
  given associativeHUpper[->[_,_], ⊙[_,_], T[_]](using a: Associative.Aux[->, ⊙, T]): AssociativeH.Aux[->, ⊙, [f[_[_]]] =>> ∀~[[a[_]] =>> T[f[a]]]] =
    new AssociativeHUpper[->, ⊙, T] { val assoc = a }
  

private object AssociativeHInstancesHelpers:
  trait AssociativeHUpper[->[_,_], ⊙[_,_], T[_]] extends AssociativeH[->, ⊙]:
    type TC[f[_[_]]] = ∀~[[a[_]] =>> T[f[a]]]
    protected def assoc: Associative.Aux[->, ⊙, T]
    def C: SubcategoryH.Aux[->, TC] = SemicategoryH.subcatHUpper[->, T](using assoc.C)
    def bifunctor: Endobifunctor[->, ⊙] = assoc.bifunctor
    def associate  [F[_[_]], G[_[_]], H[_[_]]](using F: TC[F], G: TC[G], H: TC[H]): ∀~[[a[_]] =>> ⊙[⊙[F[a], G[a]], H[a]] -> ⊙[F[a], ⊙[G[a], H[a]]]] =
      ∀~[[a[_]] =>> ⊙[⊙[F[a], G[a]], H[a]] -> ⊙[F[a], ⊙[G[a], H[a]]]](assoc.associate(using F.apply, G.apply, H.apply))
    def diassociate[F[_[_]], G[_[_]], H[_[_]]](using F: TC[F], G: TC[G], H: TC[H]): ∀~[[a[_]] =>> ⊙[F[a], ⊙[G[a], H[a]]] -> ⊙[⊙[F[a], G[a]], H[a]]] =
      ∀~[[a[_]] =>> ⊙[F[a], ⊙[G[a], H[a]]] -> ⊙[⊙[F[a], G[a]], H[a]]](assoc.diassociate(using F.apply, G.apply, H.apply))
  trait MonoidalHUpper[->[_,_], ⊙[_,_], T[_], I] extends AssociativeHUpper[->, ⊙, T] with MonoidalH[->, ⊙]:
    type Id[a[_]] = I
    protected def assoc: Monoidal.Aux[->, ⊙, T, I]
    def idl  [F[_[_]]: TC]: ∀~[[a[_]] =>> ⊙[Id[a], F[a]] -> F[a]] = ∀~[[a[_]] =>> ⊙[Id[a], F[a]] -> F[a]](assoc.idl(using summon[TC[F]].apply))
    def coidl[F[_[_]]: TC]: ∀~[[a[_]] =>> F[a] -> (Id[a] ⊙ F[a])] = ∀~[[a[_]] =>> F[a] -> (Id[a] ⊙ F[a])](assoc.coidl(using summon[TC[F]].apply))
    def idr  [F[_[_]]: TC]: ∀~[[a[_]] =>> F[a] ⊙ Id[a] -> F[a]] =   ∀~[[a[_]] =>> F[a] ⊙ Id[a] -> F[a]](assoc.idr(using summon[TC[F]].apply))
    def coidr[F[_[_]]: TC]: ∀~[[a[_]] =>> F[a] -> (F[a] ⊙ Id[a])] = ∀~[[a[_]] =>> F[a] -> (F[a] ⊙ Id[a])](assoc.coidr(using summon[TC[F]].apply))
  trait BraidedHUpper[->[_,_], ⊙[_,_], T[_]] extends AssociativeHUpper[->, ⊙, T] with BraidedH[->, ⊙]:
    protected def assoc: Braided.Aux[->, ⊙, T]
    def braid[A[_[_]]: TC, B[_[_]]: TC]: ∀~[[a[_]] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]] =
      ∀~[[a[_]] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]](assoc.braid(using summon[TC[A]].apply, summon[TC[B]].apply))
  trait SymmetricHUpper[->[_,_], ⊙[_,_], T[_]] extends BraidedHUpper[->, ⊙, T] with SymmetricH[->, ⊙]:
    protected def assoc: Symmetric.Aux[->, ⊙, T]
  trait CartesianHUpper[->[_,_], ⊙[_,_], T[_], I] extends MonoidalHUpper[->, ⊙, T, I] with SymmetricHUpper[->, ⊙, T] with CartesianH[->, ⊙]:
    protected def assoc: Cartesian.Aux[->, ⊙, T, I]
    def fst[F[_[_]]: TC, G[_[_]]: TC]: ∀~[[a[_]] =>> ⊙[F[a], G[a]] -> F[a]] = ∀~[[a[_]] =>> ⊙[F[a], G[a]] -> F[a]](assoc.fst(using summon[TC[F]].apply, summon[TC[G]].apply))
    def snd[F[_[_]]: TC, G[_[_]]: TC]: ∀~[[a[_]] =>> ⊙[F[a], G[a]] -> G[a]] = ∀~[[a[_]] =>> ⊙[F[a], G[a]] -> G[a]](assoc.snd(using summon[TC[F]].apply, summon[TC[G]].apply))
    def diag[F[_[_]]: TC]: ∀~[[a[_]] =>> F[a] -> (F[a] ⊙ F[a])] = ∀~[[a[_]] =>> F[a] -> (F[a] ⊙ F[a])](assoc.diag(using summon[TC[F]].apply))
    def &&&[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> G[a]], g: ∀~[[a[_]] =>> F[a] -> H[a]]): ∀~[[a[_]] =>> F[a] -> (G[a] ⊙ H[a])] =
      ∀~[[a[_]] =>> F[a] -> (G[a] ⊙ H[a])](assoc.&&&(f.apply, g.apply))
  trait CccHUpper[->[_,_], ⊙[_,_], |->[_,_], T[_], I] extends CartesianHUpper[->, ⊙, T, I] with CccH[->, ⊙, |->]:
    protected def assoc: Ccc.Aux[->, ⊙, |->, T, I]
    def curry  [F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> (F[a] ⊙ G[a]) -> H[a]]): ∀~[[a[_]] =>> F[a] -> (G[a] |-> H[a])] =
      ∀~[[a[_]] =>> F[a] -> (G[a] |-> H[a])](assoc.curry(f.apply))
    def uncurry[F[_[_]], G[_[_]], H[_[_]]](f: ∀~[[a[_]] =>> F[a] -> (G[a] |-> H[a])]): ∀~[[a[_]] =>> (F[a] ⊙ G[a]) -> H[a]] =
      ∀~[[a[_]] =>> (F[a] ⊙ G[a]) -> H[a]](assoc.uncurry(f.apply))
end AssociativeHInstancesHelpers
