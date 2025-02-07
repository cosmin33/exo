package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.internal.*

trait AssociativeK[->[_,_], ⊙[_,_]]:
  type TC[_[_]]
  def C: SubcategoryK.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]

  def associate  [F[_]: TC, G[_]: TC, H[_]: TC]: ∀[[a] =>> ⊙[⊙[F[a], G[a]], H[a]] -> ⊙[F[a], ⊙[G[a], H[a]]]]
  def diassociate[F[_]: TC, G[_]: TC, H[_]: TC]: ∀[[a] =>> ⊙[F[a], ⊙[G[a], H[a]]] -> ⊙[⊙[F[a], G[a]], H[a]]]

  def grouped[A[_], B[_], X[_], Y[_]](f: ∀[[a] =>> A[a] -> B[a]], g: ∀[[a] =>> X[a] -> Y[a]]): ∀[[a] =>> ⊙[A[a], X[a]] -> ⊙[B[a], Y[a]]] =
    ∀.of[[a] =>> ⊙[A[a], X[a]] -> ⊙[B[a], Y[a]]](bifunctor.bimap(f.apply, g.apply))

  def strongFirst [F[_], G[_], H[_]: TC](fa: ∀[[a] =>> F[a] -> G[a]]): ∀[[a] =>> ⊙[H[a], F[a]] -> ⊙[H[a], G[a]]] = grouped(C.id[H], fa)
  def strongSecond[F[_], G[_], H[_]: TC](fa: ∀[[a] =>> F[a] -> G[a]]): ∀[[a] =>> ⊙[F[a], H[a]] -> ⊙[G[a], H[a]]] = grouped(fa, C.id[H])

  private type <->[a[_], b[_]] = IsoK[->, a, b]
  def isoAssociator[F[_]: TC, G[_]: TC, H[_]: TC]: ([a] =>> ⊙[⊙[F[a], G[a]], H[a]]) <-> ([a] =>> ⊙[F[a], ⊙[G[a], H[a]]]) =
    IsoK.unsafe[->, [a] =>> ⊙[⊙[F[a], G[a]], H[a]], [a] =>> ⊙[F[a], ⊙[G[a], H[a]]]](associate[F,G,H], diassociate[F,G,H])(using C.lower)

object AssociativeK extends AssociativeKInstances:
  type Aux[->[_,_], ⊙[_,_], TC0[_[_]]] = AssociativeK[->, ⊙] { type TC[A[_]] = TC0[A] }
  def apply[->[_,_], ⊙[_,_]](using ev: AssociativeK[->, ⊙]): AssociativeK[->, ⊙] = ev
end AssociativeK

import AssociativeKInstancesHelpers.*

trait AssociativeKInstances extends AssociativeKInstances01:
  given cccKUpper[->[_,_], ⊙[_,_], |->[_,_], T[_], I](using c: Ccc.Aux[->, ⊙, |->, T, I]): CccK.Aux[->, ⊙, |->, [f[_]] =>> ∀[[a] =>> T[f[a]]], [a] =>> I] =
    new CccKUpper[->, ⊙, |->, T, I] { val assoc = c }

trait AssociativeKInstances01 extends AssociativeKInstances02:
  given cartesianKUpper[->[_,_], ⊙[_,_], T[_], I](using c: Cartesian.Aux[->, ⊙, T, I]): CartesianK.Aux[->, ⊙, [f[_]] =>> ∀[[a] =>> T[f[a]]], [a] =>> I] =
    new CartesianKUpper[->, ⊙, T, I] { val assoc = c }

trait AssociativeKInstances02 extends AssociativeKInstances03:
  given monoidalKUpper[->[_,_], ⊙[_,_], T[_], I](using m: Monoidal.Aux[->, ⊙, T, I]): MonoidalK.Aux[->, ⊙, [f[_]] =>> ∀[[a] =>> T[f[a]]], [a] =>> I] =
    new MonoidalKUpper[->, ⊙, T, I] { val assoc = m }

trait AssociativeKInstances03 extends AssociativeKInstances04:
  given symmetricKUpper[->[_,_], ⊙[_,_], T[_]](using s: Symmetric.Aux[->, ⊙, T]): SymmetricK.Aux[->, ⊙, [f[_]] =>> ∀[[a] =>> T[f[a]]]] =
    new SymmetricKUpper[->, ⊙, T] { val assoc = s }

trait AssociativeKInstances04 extends AssociativeKInstances05:
  given braidedKUpper[->[_,_], ⊙[_,_], T[_]](using b: Braided.Aux[->, ⊙, T]): BraidedK.Aux[->, ⊙, [f[_]] =>> ∀[[a] =>> T[f[a]]]] =
    new BraidedKUpper[->, ⊙, T] { val assoc = b }

trait AssociativeKInstances05:
  given associativeKUpper[->[_,_], ⊙[_,_], T[_]](using a: Associative.Aux[->, ⊙, T]): AssociativeK.Aux[->, ⊙, [f[_]] =>> ∀[[a] =>> T[f[a]]]] =
    new AssociativeKUpper[->, ⊙, T] { val assoc = a }

private object AssociativeKInstancesHelpers:
  trait AssociativeKUpper[->[_,_], ⊙[_,_], T[_]] extends AssociativeK[->, ⊙]:
    type TC[f[_]] = ∀[[a] =>> T[f[a]]]
    protected def assoc: Associative.Aux[->, ⊙, T]
    def C: SubcategoryK.Aux[->, TC] = SemicategoryK.subcatKUpper[->, T](using assoc.C)
    def bifunctor: Endobifunctor[->, ⊙] = assoc.bifunctor
    def associate  [F[_], G[_], H[_]](using F: TC[F], G: TC[G], H: TC[H]): ∀[[a] =>> ⊙[⊙[F[a], G[a]], H[a]] -> ⊙[F[a], ⊙[G[a], H[a]]]] =
      ∀[[a] =>> ⊙[⊙[F[a], G[a]], H[a]] -> ⊙[F[a], ⊙[G[a], H[a]]]](assoc.associate(using F.apply, G.apply, H.apply))
    def diassociate[F[_], G[_], H[_]](using F: TC[F], G: TC[G], H: TC[H]): ∀[[a] =>> ⊙[F[a], ⊙[G[a], H[a]]] -> ⊙[⊙[F[a], G[a]], H[a]]] =
      ∀[[a] =>> ⊙[F[a], ⊙[G[a], H[a]]] -> ⊙[⊙[F[a], G[a]], H[a]]](assoc.diassociate(using F.apply, G.apply, H.apply))
  trait MonoidalKUpper[->[_,_], ⊙[_,_], T[_], I] extends AssociativeKUpper[->, ⊙, T] with MonoidalK[->, ⊙]:
    type Id[a] = I
    protected def assoc: Monoidal.Aux[->, ⊙, T, I]
    def idl  [F[_]: TC]: ∀[[a] =>> Id[a] ⊙ F[a] -> F[a]] = ∀[[a] =>> Id[a] ⊙ F[a] -> F[a]](assoc.idl(using summon[TC[F]].apply))
    def coidl[F[_]: TC]: ∀[[a] =>> F[a] -> (I ⊙ F[a])] =   ∀[[a] =>> F[a] -> (I ⊙ F[a])](assoc.coidl(using summon[TC[F]].apply))
    def idr  [F[_]: TC]: ∀[[a] =>> F[a] ⊙ I -> F[a]] =     ∀[[a] =>> F[a] ⊙ I -> F[a]](assoc.idr(using summon[TC[F]].apply))
    def coidr[F[_]: TC]: ∀[[a] =>> F[a] -> (F[a] ⊙ I)] =   ∀[[a] =>> F[a] -> (F[a] ⊙ I)](assoc.coidr(using summon[TC[F]].apply))
  trait BraidedKUpper[->[_,_], ⊙[_,_], T[_]] extends AssociativeKUpper[->, ⊙, T] with BraidedK[->, ⊙]:
    protected def assoc: Braided.Aux[->, ⊙, T]
    def braid[A[_]: TC, B[_]: TC]: ∀[[a] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]] =
      ∀[[a] =>> ⊙[A[a], B[a]] -> ⊙[B[a], A[a]]](assoc.braid(using summon[TC[A]].apply, summon[TC[B]].apply))
  trait SymmetricKUpper[->[_,_], ⊙[_,_], T[_]] extends BraidedKUpper[->, ⊙, T] with SymmetricK[->, ⊙]:
    protected def assoc: Symmetric.Aux[->, ⊙, T]
  trait CartesianKUpper[->[_,_], ⊙[_,_], T[_], I] extends MonoidalKUpper[->, ⊙, T, I] with SymmetricKUpper[->, ⊙, T] with CartesianK[->, ⊙]:
    protected def assoc: Cartesian.Aux[->, ⊙, T, I]
    def fst[F[_]: TC, G[_]: TC]: ∀[[a] =>> F[a] ⊙ G[a] -> F[a]] = ∀[[a] =>> F[a] ⊙ G[a] -> F[a]](assoc.fst(using summon[TC[F]].apply, summon[TC[G]].apply))
    def snd[F[_]: TC, G[_]: TC]: ∀[[a] =>> F[a] ⊙ G[a] -> G[a]] = ∀[[a] =>> F[a] ⊙ G[a] -> G[a]](assoc.snd(using summon[TC[F]].apply, summon[TC[G]].apply))
    def diag[F[_]: TC]: ∀[[a] =>> F[a] -> (F[a] ⊙ F[a])] = ∀[[a] =>> F[a] -> (F[a] ⊙ F[a])](assoc.diag(using summon[TC[F]].apply))
    def &&&[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> G[a]], g: ∀[[a] =>> F[a] -> H[a]]): ∀[[a] =>> F[a] -> (G[a] ⊙ H[a])] =
      ∀[[a] =>> F[a] -> (G[a] ⊙ H[a])](assoc.&&&(f.apply, g.apply))
  trait CccKUpper[->[_,_], ⊙[_,_], |->[_,_], T[_], I] extends CartesianKUpper[->, ⊙, T, I] with CccK[->, ⊙, |->]:
    protected def assoc: Ccc.Aux[->, ⊙, |->, T, I]
    def curry  [F[_], G[_], H[_]](f: ∀[[a] =>> (F[a] ⊙ G[a]) -> H[a]]): ∀[[a] =>> F[a] -> (G[a] |-> H[a])] =
      ∀[[a] =>> F[a] -> (G[a] |-> H[a])](assoc.curry(f.apply))
    def uncurry[F[_], G[_], H[_]](f: ∀[[a] =>> F[a] -> (G[a] |-> H[a])]): ∀[[a] =>> (F[a] ⊙ G[a]) -> H[a]] =
      ∀[[a] =>> (F[a] ⊙ G[a]) -> H[a]](assoc.uncurry(f.apply))
end AssociativeKInstancesHelpers
