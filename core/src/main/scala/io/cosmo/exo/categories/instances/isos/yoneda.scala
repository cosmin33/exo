package io.cosmo.exo.categories.instances.isos

import cats.implicits._
import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.evidence.{<~<, ===}

object yoneda {
  /** yoneda lemma for covariant functor */
  def lemmaYoIso[->[_,_], A, F[_]](implicit
    C: SubcatHasId[->, A], E: Exo.Cov[->, F]
  ): ((A -> *) ~> F) <=> F[A] = Iso.unsafe(_[A](C.id), fa => ∀.of[λ[x => A -> x => F[x]]].from(E.map(_)(fa)))
  /** yoneda lemma for contravariant functor */
  def lemmaCoyoIso[->[_,_], A, F[_]](implicit
    C: SubcatHasId[->, A], E: Exo.Con[->, F]
  ): ((* -> A) ~> F) <=> F[A] =
    Iso.unsafe(_[A](C.id), fa => ∀.of[λ[x => x -> A => F[x]]].from(xa => E.map(Dual(xa))(fa)))

  private def lemmaYoUnrestricted  [A, F[_]]: ((A === *) ~> F) <=> F[A] = lemmaYoIso  [===, A, F]
  private def lemmaCoyoUnrestricted[A, F[_]]: ((* === A) ~> F) <=> F[A] = lemmaCoyoIso[===, A, F]

  def yoEmbeddingCov[->[_,_], A, B](implicit
    C: SubcatHasId[->, A]
  ): ((A -> *) ~> (B -> *)) <=> (B -> A) = lemmaYoIso[->, A, B -> *](C, Exo.semiFunctorCov(C.s))
  def yoEmbeddingCon[->[_,_], A, B](implicit
    C: SubcatHasId[->, A]
  ): ((* -> A) ~> (* -> B)) <=> (A -> B) = lemmaCoyoIso[->, A, * -> B](C, Exo.semiFunctorCon(C.s))

  def yoDoubleEmbed[->[_,_], A, B](implicit
    cat: Subcat[->]
  ): (A -> B) <=> ∀~[λ[f[_] => Endofunctor[->, f] => f[A] -> f[B]]] =
    Iso.unsafe(
      ab => ∀~.of[λ[f[_] => Endofunctor[->, f] => f[A] -> f[B]]].from(_.map(ab)),
      fa => fa.apply[λ[a => a]](Exo.idEndofunctor)
    )

  def yoCorol1Cov[->[_,_], A, B](implicit
    ca: SubcatHasId[->, A], cb: SubcatHasId[->, B]
  ): ((A -> *) <~> (B -> *)) <=> Iso[->, B, A] =
      Iso.unsafe(
        i => Iso.unsafe(i.apply[A].to(ca.id), i.apply[B].from(cb.id))(ca.s),
        i => <~>.unsafe(yoEmbeddingCov[->, A, B].from(i.to), yoEmbeddingCov[->, B, A].from(i.from))
      )

  def yoCorol1Con[->[_,_], A, B](implicit
    ca: SubcatHasId[->, A], cb: SubcatHasId[->, B]
  ): ((* -> A) <~> (* -> B)) <=> Iso[->, A, B] =
    Iso.unsafe(
      i => Iso.unsafe(i.apply[A].to(ca.id), i.apply[B].from(cb.id))(ca.s),
      i => <~>.unsafe(yoEmbeddingCon[->, A, B].from(i.to), yoEmbeddingCon[->, B, A].from(i.from))
    )

  private def isoIndirectLiskov [A, B]: ((A <~< *)  ~> (B <~< *)) <=> (B <~< A) = yoEmbeddingCov
  private def isoIndirectLeibniz[A, B]: ((A === *)  ~> (B === *)) <=> (A === B) = yoEmbeddingCov[===, A, B] andThen Iso.isoGroupoidFlip
  private def isoIndirectLeibni_[A, B]: ((A === *) <~> (B === *)) <=> (A === B) =
    yoCorol1Cov[===, A, B] andThen Iso.isoGroupoid[===, B, A].flip andThen Iso.isoGroupoidFlip
//     yoCorol1Cov[===, A, B].chain[B === A].chain[A === B] // strange compile error for this one but it should work, I think it's a scala bug ?!?!
    // TODO: investigate why the above doesn't work

  /** object containing all general yoneda isomorphisms applied to Function1 */
  object function1 {
    /** yoneda lemma covariant for Function1 */
    def lemmaYoIso  [A, F[_]: Exo.CovF]: ((A => *) ~> F) <=> F[A] = yoneda.lemmaYoIso
    /** yoneda lemma contravariant for Function1 */
    def lemmaCoyoIso[A, F[_]: Exo.ConF]: ((* => A) ~> F) <=> F[A] = yoneda.lemmaCoyoIso
    /** yoneda embedding - covariant for Function1 */
    def yoEmbedding  [A, B]: ((A => *) ~> (B => *)) <=> (B => A) = lemmaYoIso  [A, B => *]
    /** yoneda embedding - contravariant for Function1 */
    def coyoEmbedding[A, B]: ((* => A) ~> (* => B)) <=> (A => B) = lemmaCoyoIso[A, * => B]
    /** yoneda embedding corollary 1 - covariant for Function1 */
    def yoCorol1Cov[A, B]: ((A => *) <~> (B => *)) <=> (B <=> A) = yoneda.yoCorol1Cov
    /** yoneda embedding corollary 1 - contravariant for Function1 */
    def yoCorol1Con[A, B]: ((* => A) <~> (* => B)) <=> (A <=> B) = yoneda.yoCorol1Con
  }

}
