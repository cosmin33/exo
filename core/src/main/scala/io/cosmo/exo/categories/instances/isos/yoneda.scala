package io.cosmo.exo.categories.instances.isos

import cats.free.{Coyoneda, Yoneda}
import cats.implicits._
import cats.{Contravariant, Functor, Id}
import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.evidence.{<~<, ===, Is}
import io.cosmo.exo.categories.conversions.CatsInstances._
import io.cosmo.exo.evidence.variance.IsCovariant

object yoneda {

  implicit def yonedaIso1  [F[_]: Functor, A]: F[A] <=> Yoneda[F, A]   = Iso.unsafe(Yoneda(_), _(identity))
  implicit def coyonedaIso1[F[_]: Functor, A]: F[A] <=> Coyoneda[F, A] = Iso.unsafe(Coyoneda.lift, _.run)

  /** yoneda lemma covariant (generic category) */
  def lemmaYoIsoCov[->[_,_], ->#[_], A, F[_]](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Cov[->, F]
//  ): ((A -> *) ~> F) <=> F[A] =
  ): ∀[λ[x => A -> x => F[x]]] <=> F[A] =
    Iso.unsafe(_[A](C.id), fa => ∀.of[λ[x => A -> x => F[x]]].from(E.map(_)(fa)))
  /** yoneda lemma contravariant (generic category) */
  def lemmaYoIsoCon[->[_,_], ->#[_], A, F[_]](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Con[->, F]
  ): ∀[λ[x => x -> A => F[x]]] <=> F[A] =
    Iso.unsafe(_[A](C.id[A]), fa => ∀.of[λ[x => x -> A => F[x]]].from(xa => E.map(Dual(xa))(fa)))

  def yoEmbeddingCov[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Cov[->, B -> *]
  ): ((A -> *) ~> (B -> *)) <=> (B -> A) = lemmaYoIsoCov[->, ->#, A, B -> *]
  def yoEmbeddingCon[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Con[->, * -> B]
  ): ((* -> A) ~> (* -> B)) <=> (A -> B) = lemmaYoIsoCon[->, ->#, A, * -> B]

  def isoIndirectLiskov[A, B]: ((A <~< *) ~> (B <~< *)) <=> (B <~< A) = yoEmbeddingCov[<~<, Trivial.T1, A, B]
  def isoIndirectLeibniz[A, B]: ((A === *) <~> (B === *)) <=> (A === B) =
    yoCorol1Cov[===, Trivial.T1, A, B].andThen(Groupoid.isoIso[===, B, A].flip).andThen(Groupoid.isoFlip)

  def yoEmbedCovTo[->[_,_], A, B, ->#[_]](fa: (A -> *) ~> (B -> *))(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Cov[->, B -> *]
  ): B -> A = yoEmbeddingCov.to(fa)
  def yoEmbedConTo[->[_,_], A, B, ->#[_]](fa: (* -> A) ~> (* -> B))(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Con[->, * -> B]
  ): A -> B = yoEmbeddingCon.to(fa)
  def yoEmbedCovFrom[->[_,_], A, B, ->#[_]](ba: B -> A)(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Cov[->, B -> *]
  ): (A -> *) ~> (B -> *) = yoEmbeddingCov.from(ba)
  def yoEmbedConFrom[->[_,_], A, B, ->#[_]](ab: A -> B)(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Con[->, * -> B]
  ): (* -> A) ~> (* -> B) = yoEmbeddingCon.from(ab)

  def yoDoubleEmbed[->[_,_], ->#[_], A, B](implicit
    cat: Subcat.Aux[->, ->#],
    F: Endofunctor[->, λ[a => a]]
  ): (A -> B) <=> ∀~[λ[f[_] => Endofunctor[->, f] => f[A] -> f[B]]] = {
    Iso.unsafe(
      ab => ∀~.of[λ[f[_] => Endofunctor[->, f] => f[A] -> f[B]]].from(_.map(ab)),
      fa => fa.apply[λ[a => a]](F)
    )
  }

  def yoCorol1Cov[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tca: ->#[A], tcb: ->#[B],
    Ea: Exo.Cov[->, A -> *],
    Eb: Exo.Cov[->, B -> *],
  ): ((A -> *) <~> (B -> *)) <=> Iso[->, B, A] =
      Iso.unsafe(fa => Iso.unsafe(fa[A].to(C.id[A]), fa[B].from(C.id[B])),
                 ba => <~>.unsafe[A -> *, B -> *](yoEmbedCovFrom(ba.to), yoEmbedCovFrom(ba.from)))

  def yoCorol1Con[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tca: ->#[A], tcb: ->#[B],
    Ea: Exo.Con[->, * -> A],
    Eb: Exo.Con[->, * -> B],
  ): ((* -> A) <~> (* -> B)) <=> Iso[->, A, B] =
    Iso.unsafe(i => Iso.unsafe(i[A].to(C.id[A]), i[B].from(C.id[B])),
               i => <~>.unsafe[* -> A, * -> B](yoEmbedConFrom(i.to), yoEmbedConFrom(i.from)))

  /** object containing all general yoneda isomorphisms applied to Function1 */
  object function1 {
    /** yoneda lemma covariant for Function1 */
    def lemmaYoIso[A, F[_]: Exo.CovF]: ((A => *) ~> F) <=> F[A] =   yoneda.lemmaYoIsoCov[* => *, Trivial.T1, A, F]
    /** yoneda lemma contravariant for Function1 */
    def lemmaCoyoIso[A, F[_]: Exo.ConF]: ((* => A) ~> F) <=> F[A] = yoneda.lemmaYoIsoCon[* => *, Trivial.T1, A, F]
    /** yoneda embedding - covariant for Function1 */
    def yoEmbedding  [A, B]: ((A => *) ~> (B => *)) <=> (B => A) = lemmaYoIso  [A, B => *]
    /** yoneda embedding - contravariant for Function1 */
    def coyoEmbedding[A, B]: ((* => A) ~> (* => B)) <=> (A => B) = lemmaCoyoIso[A, * => B]
    /** yoneda embedding corollary 1 - covariant for Function1 */
    def yoCorol1Cov[A, B]: ((A => *) <~> (B => *)) <=> (B <=> A) = yoneda.yoCorol1Cov[* => *, Trivial.T1, A, B]
    /** yoneda embedding corollary 1 - contravariant for Function1 */
    def yoCorol1Con[A, B]: ((* => A) <~> (* => B)) <=> (A <=> B) = yoneda.yoCorol1Con[* => *, Trivial.T1, A, B]
  }

}
