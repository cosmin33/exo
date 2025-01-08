package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.syntax.*

import scala.util.NotGiven

trait IsoK2[->[_,_], F[_,_], G[_,_]]:
  self =>

  def cat: SemicategoryK2[->]

  def to  [A, B]: F[A, B] -> G[A, B]
  def from[A, B]: G[A, B] -> F[A, B]

  def forallTo:   ∀∀[[a, b] =>> F[a, b] -> G[a, b]] = ∀∀.of[[a, b] =>> F[a, b] -> G[a, b]](self.to)
  def forallFrom: ∀∀[[a, b] =>> G[a, b] -> F[a, b]] = ∀∀.of[[a, b] =>> G[a, b] -> F[a, b]](self.from)

  def lower[A, B](using Subcategory[->]): Iso[->, F[A, B], G[A, B]] = Iso.unsafe(self.to[A, B], self.from[A, B])
  def forall(using Subcategory[->]): ∀∀[[a, b] =>> Iso[->, F[a, b], G[a, b]]] = ∀∀[[a, b] =>> Iso[->, F[a, b], G[a, b]]](lower)

  private type <->[f[_,_], g[_,_]] = IsoK2[->, f, g]

  lazy val flip: G <-> F =
    new IsoK2[->, G, F]:
      def cat = self.cat
      def to  [A, B] = self.from[A, B]
      def from[A, B] = self.to[A, B]
      override lazy val flip = self

  private[this] given SemicategoryK2[->] = cat

  def andThen[H[_,_]](that: G <-> H): F <-> H =
    new IsoK2[->, F, H]:
      def cat = self.cat
      def to  [A, B] = (self.forallTo >>> that.forallTo)[A, B]
      def from[A, B] = (that.forallFrom >>> self.forallFrom)[A, B]

  def compose[E[_,_]](that: E <-> F): E <-> G = that andThen this

  def teleport(f: ∀∀[[a, b] =>> F[a, b] -> F[a, b]]): ∀∀[[a, b] =>> G[a, b] -> G[a, b]] = self.forallFrom >>> f >>> self.forallTo

  def chain[H[_,_]](that: HasIsoK2[->, G, H]): F <-> H = andThen(that)

  def derive[A[_[_,_]]](using t: A[F], I: ExofunctorK2[->, * => *, A]): A[G] = I.map[F, G](self.forallTo)(t)

  def grouped[⨂[_,_]] = new GroupedPartial[⨂]
  class GroupedPartial[⨂[_,_]]:
    def apply[X[_,_], Y[_,_]](that: X <-> Y)(using A: AssociativeK2[->, ⨂]): ([a, b] =>> F[a, b] ⨂ X[a, b]) <-> ([a, b] =>> G[a, b] ⨂ Y[a, b]) =
      IsoK2.unsafe(A.grouped(self.forallTo, that.forallTo), A.grouped(self.forallFrom, that.forallFrom))

object IsoK2:
  def apply[->[_,_], F[_,_], G[_,_]](using iso: HasIsoK2[->, F, G]): IsoK2[->, F, G] = iso
  def apply[->[_,_], F[_,_]](using SubcatK2HasId[->, F]): IsoK2[->, F, F] = IsoK2.refl
  def apply[F[_,_]]: F <~~> F = IsoK2.refl

  /** create an isomorphism given the two complementary functions as long as you promise they uphold the iso laws */
  def unsafe[->[_,_], F[_,_], G[_,_]](fg: ∀∀[[a, b] =>> F[a, b] -> G[a, b]], gf: ∀∀[[a, b] =>> G[a, b] -> F[a, b]])(using C: SemicategoryK2[->]): IsoK2[->, F, G] =
    new IsoK2[->, F, G]:
      def cat = C
      def to  [A, B] = fg[A, B]
      def from[A, B] = gf[A, B]

  def refl[->[_,_], F[_,_]](using C: SubcatK2HasId[->, F]): IsoK2[->, F, F] = unsafe(C.id, C.id)(using C.s)

end IsoK2