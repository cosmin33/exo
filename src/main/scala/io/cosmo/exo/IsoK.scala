package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.syntax.*

import scala.util.NotGiven

trait IsoK[->[_,_], F[_], G[_]]:
  self =>

  def cat: SemicategoryK[->]

  def to  [A]: F[A] -> G[A]
  def from[A]: G[A] -> F[A]

  def toK:   ∀[[a] =>> F[a] -> G[a]] = ∀.of[[a] =>> F[a] -> G[a]](self.to)
  def fromK: ∀[[a] =>> G[a] -> F[a]] = ∀.of[[a] =>> G[a] -> F[a]](self.from)

  def lower[A](using Subcategory[->]): Iso[->, F[A], G[A]] = Iso.unsafe(self.to[A], self.from[A])
  def forall(using Subcategory[->]): ∀[[a] =>> Iso[->, F[a], G[a]]] = ∀[[a] =>> Iso[->, F[a], G[a]]](lower)

  private type <->[f[_], g[_]] = IsoK[->, f, g]

  lazy val flip: G <-> F =
    new IsoK[->, G, F]:
      def cat = self.cat
      def to  [A] = self.from[A]
      def from[A] = self.to[A]
      override lazy val flip = self

  private[this] given SemicategoryK[->] = cat

  def andThen[H[_]](that: G <-> H): F <-> H =
    new IsoK[->, F, H]:
      def cat = self.cat
      def to  [A] = (self.toK >>> that.toK)[A]
      def from[A] = (that.fromK >>> self.fromK)[A]

  def compose[E[_]](that: E <-> F): E <-> G = that andThen this

  def teleport(f: ∀[[a] =>> F[a] -> F[a]]): ∀[[a] =>> G[a] -> G[a]] = self.fromK >>> f >>> self.toK

  def chain[H[_]](that: HasIsoK[->, G, H]): F <-> H = andThen(that)

  def derive[A[_[_]]](using t: A[F], I: ExofunctorK[->, * => *, A]): A[G] = I.map[F, G](self.toK)(t)

  def grouped[⨂[_,_]] = new GroupedPartial[⨂]
  class GroupedPartial[⨂[_,_]]:
    def apply[X[_], Y[_]](that: X <-> Y)(using A: AssociativeK[->, ⨂]): ([a] =>> F[a] ⨂ X[a]) <-> ([a] =>> G[a] ⨂ Y[a]) =
      IsoK.unsafe(A.grouped(self.toK, that.toK), A.grouped(self.fromK, that.fromK))

object IsoK:
  def apply[->[_,_], F[_], G[_]](using iso: HasIsoK[->, F, G]): IsoK[->, F, G] = iso
  def apply[->[_,_], F[_]](using SubcatKHasId[->, F]): IsoK[->, F, F] = IsoK.refl
  def apply[F[_]]: F <~> F = IsoK.refl

  /** create an isomorphism given the two complementary functions as long as you promise they uphold the iso laws */
  def unsafe[->[_,_], F[_], G[_]](fg: ∀[[a] =>> F[a] -> G[a]], gf: ∀[[a] =>> G[a] -> F[a]])(using C: SemicategoryK[->]): IsoK[->, F, G] =
    new IsoK[->, F, G]:
      def cat = C
      def to  [A] = fg[A]
      def from[A] = gf[A]

  def refl[->[_,_], F[_]](using C: SubcatKHasId[->, F]): IsoK[->, F, F] = unsafe(C.id, C.id)(using C.s)

  
end IsoK
