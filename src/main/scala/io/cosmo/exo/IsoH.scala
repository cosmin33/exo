package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.syntax.*

import scala.util.NotGiven

trait IsoH[->[_,_], F[_[_]], G[_[_]]]:
  self =>

  def cat: SemicategoryH[->]

  def to  [A[_]]: F[A] -> G[A]
  def from[A[_]]: G[A] -> F[A]

  def forallTo:   ∀~[[a[_]] =>> F[a] -> G[a]] = ∀~.of[[a[_]] =>> F[a] -> G[a]](self.to)
  def forallFrom: ∀~[[a[_]] =>> G[a] -> F[a]] = ∀~.of[[a[_]] =>> G[a] -> F[a]](self.from)

  def lower[X[_]](using Subcategory[->]): Iso[->, F[X], G[X]] = Iso.unsafe(self.to[X], self.from[X])
  def forall(using Subcategory[->]): ∀~[[a[_]] =>> Iso[->, F[a], G[a]]] = ∀~[[a[_]] =>> Iso[->, F[a], G[a]]](lower)

  private type <->[f[_[_]], g[_[_]]] = IsoH[->, f, g]

  lazy val flip: G <-> F =
    new IsoH[->, G, F]:
      def cat = self.cat
      def to  [A[_]] = self.from[A]
      def from[A[_]] = self.to[A]
      override lazy val flip = self

  private[this] given SemicategoryH[->] = cat

  def andThen[H[_[_]]](that: G <-> H): F <-> H =
    new IsoH[->, F, H]:
      def cat = self.cat
      def to  [A[_]] = (self.forallTo >>> that.forallTo)[A]
      def from[A[_]] = (that.forallFrom >>> self.forallFrom)[A]

  def compose[E[_[_]]](that: E <-> F): E <-> G = that andThen this

  def teleport(f: ∀~[[a[_]] =>> F[a] -> F[a]]): ∀~[[a[_]] =>> G[a] -> G[a]] = self.forallFrom >>> f >>> self.forallTo

  def chain[H[_[_]]](that: HasIsoH[->, G, H]): F <-> H = andThen(that)

  def derive[A[_[_[_]]]](using t: A[F], I: ExofunctorH[->, * => *, A]): A[G] = I.map[F, G](self.forallTo)(t)

  def grouped[⨂[_,_]] = new GroupedPartial[⨂]
  class GroupedPartial[⨂[_,_]]:
    def apply[X[_[_]], Y[_[_]]](that: X <-> Y)(using A: AssociativeH[->, ⨂]): ([a[_]] =>> F[a] ⨂ X[a]) <-> ([a[_]] =>> G[a] ⨂ Y[a]) =
      IsoH.unsafe(A.grouped(self.forallTo, that.forallTo), A.grouped(self.forallFrom, that.forallFrom))

object IsoH:
  def apply[->[_,_], F[_[_]], G[_[_]]](using iso: HasIsoH[->, F, G]): IsoH[->, F, G] = iso
  def apply[->[_,_], F[_[_]]](using SubcatHHasId[->, F]): IsoH[->, F, F] = IsoH.refl
  def apply[F[_[_]]]: F <≈> F = IsoH.refl

  /** create an isomorphism given the two complementary functions as long as you promise they uphold the iso laws */
  def unsafe[->[_,_], F[_[_]], G[_[_]]](fg: ∀~[[a[_]] =>> F[a] -> G[a]], gf: ∀~[[a[_]] =>> G[a] -> F[a]])(using C: SemicategoryH[->]): IsoH[->, F, G] =
    new IsoH[->, F, G]:
      def cat = C
      def to  [A[_]] = fg[A]
      def from[A[_]] = gf[A]

  def refl[->[_,_], F[_[_]]](using C: SubcatHHasId[->, F]): IsoH[->, F, F] = unsafe(C.id, C.id)(using C.s)

end IsoH
