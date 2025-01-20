package io.cosmo.exo

import io.cosmo.exo
import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*

object yoneda {
  /** yoneda lemma for covariant functor */
  def lemmaYoIso[->[_,_], A, F[_]](using
    C: SubcatHasId[->, A], E: Exo.Cov[->, F]
  ): (->[A,*] ~> F) <=> F[A] = Iso.unsafe(_[A](C.id), fa => ∀[[o] =>> A -> o => F[o]](E.map(_)(fa)))
  /** yoneda lemma for contravariant functor */
  def lemmaCoyoIso[->[_,_], A, F[_]](using
    C: SubcatHasId[->, A], E: Exo.Con[->, F]
  ): (->[*,A] ~> F) <=> F[A] =
    Iso.unsafe(_[A](C.id), fa => ∀[[o] =>> o -> A => F[o]](xa => E.map(Dual(xa))(fa)))

  def yoEmbeddingGeneric[-->[_,_], ==>[_,_], A, B](using
    C: SubcatHasId[-->, A], F: Exo.Cov[-->, [o] =>> B ==> o]
  ): (-->[A,*] ~> ==>[B,*]) <=> (B ==> A) = lemmaYoIso[-->, A, [o] =>> B ==> o]

  def coyoEmbeddingGeneric[-->[_,_], ==>[_,_], A, B](using
    C: SubcatHasId[-->, A], F: Exo.Con[-->, [o] =>> o ==> B]
  ): (-->[*,A] ~> ==>[*,B]) <=> (A ==> B) = lemmaCoyoIso[-->, A, [o] =>> o ==> B]

  def yoEmbedding[->[_,_], A, B](using
    C: SubcatHasId[->, A]
  ): (->[A,*] ~> ->[B,*]) <=> (B -> A) = lemmaYoIso[->, A, [o] =>> B -> o](using C, Exo.semiFunctorCov(using C.s))
  def coyoEmbedding[->[_,_], A, B](using
    C: SubcatHasId[->, A]
  ): (->[*,A] ~> ->[*,B]) <=> (A -> B) = lemmaCoyoIso[->, A, [o] =>> o -> B](using C, Exo.semiFunctorCon(using C.s))

  def yoDoubleEmbed[->[_,_], A, B](using
    cat: Subcat[->]
  ): (A -> B) <=> ∀~[[f[_]] =>> Endofunctor[->, f] => f[A] -> f[B]] =
    Iso.unsafe(
      ab => ∀~.of[[f[_]] =>> Endofunctor[->, f] => f[A] -> f[B]].from(_.map(ab)),
      fa => fa.apply[[a] =>> a](Exo.idEndofunctor)
    )

  def yoCorollary[->[_,_], A, B](using
    ca: SubcatHasId[->, A], cb: SubcatHasId[->, B]
  ): (->[A,*] <~> ->[B,*]) <=> Iso[->, B, A] =
      Iso.unsafe(
        i => Iso.unsafe(i.apply[A].to(ca.id), i.apply[B].from(cb.id))(using ca.s),
        i => <~>.unsafe(yoEmbedding[->, A, B].from(i.to), yoEmbedding[->, B, A].from(i.from))
      )

  def coyoCorollary[->[_,_], A, B](using
    ca: SubcatHasId[->, A], cb: SubcatHasId[->, B]
  ): (->[*,A] <~> ->[*,B]) <=> Iso[->, A, B] =
    Iso.unsafe(
      i => Iso.unsafe(i.apply[A].to(ca.id), i.apply[B].from(cb.id))(using ca.s),
      i => <~>.unsafe[->[*,A], ->[*,B]](coyoEmbedding[->, A, B].from(i.to), coyoEmbedding[->, B, A].from(i.from))
    )

  /** object containing all general yoneda isomorphisms applied to Function1 */
  object function1 {
    /** yoneda lemma - covariant functors on Function1 */
    def lemmaYoIso  [A, F[_]: Exo.CovF]: ((A => *) ~> F) <=> F[A] = yoneda.lemmaYoIso  [* => *, A, F]
    /** yoneda lemma - contravariant functors on Function1 */
    def lemmaCoyoIso[A, F[_]: Exo.ConF]: ((* => A) ~> F) <=> F[A] = yoneda.lemmaCoyoIso[* => *, A, F]
    /** yoneda embedding - covariant functors on Function1 */
    def yoEmbedding  [A, B]: ((A => *) ~> (B => *)) <=> (B => A) = lemmaYoIso  [A, B => *]
    /** yoneda embedding - contravariant functors on Function1 */
    def coyoEmbedding[A, B]: ((* => A) ~> (* => B)) <=> (A => B) = lemmaCoyoIso[A, * => B]
    /** yoneda embedding corollary 1 - covariant functors on Function1 */
    def yoCorol1  [A, B]: ((A => *) <~> (B => *)) <=> (B <=> A) = yoneda.yoCorollary[* => *, A, B]
    /** yoneda embedding corollary 1 - contravariant functors on Function1 */
    def coyoCorol1[A, B]: ((* => A) <~> (* => B)) <=> (A <=> B) = yoneda.coyoCorollary[* => *, A, B]
  }

  // applied yoneda examples
  private def lemmaYoUnrestricted  [A, F[_]]: (===[A,*] ~> F) <=> F[A] = lemmaYoIso  [===, A, F]
  private def lemmaCoyoUnrestricted[A, F[_]]: (===[*,A] ~> F) <=> F[A] = lemmaCoyoIso[===, A, F]

  private def isoIndirectLiskov [A, B]: ∀[[a] =>> (A <~< a)  => (B <~< a)] <=> (B <~< A) = yoEmbedding
  private def isoIndirectLeibniz[A, B]: ∀[[a] =>> (A === a)  => (B === a)] <=> (A === B) = yoEmbedding[===, A, B] andThen Iso.isoGroupoidFlip
  private def isoIndirectLeibni_[A, B]: ∀[[a] =>> (A === a) <=> (B === a)] <=> (A === B) =
    yoCorollary[===, A, B] andThen Iso.isoGroupoid[===, B, A].flip andThen Iso.isoGroupoidFlip
}

object yonedaK {
  def lemmaYoIsoK[->[_,_], F[_], A[_[_]]](using
    C: SubcatKHasId[->, F], E: ExofunctorK[->, * => *, A]
  ): (([G[_]] =>> ∀[[a] =>> F[a] -> G[a]]) ≈> A) <=> A[F] =
    Iso.unsafe(
      _[F](C.id),
      af => ∀~[[G[_]] =>> ∀[[a] =>> F[a] -> G[a]] => A[G]].fromH([G[_]] => () => (fg: ∀[[a] =>> F[a] -> G[a]]) => E.map(fg)(af))
    )

  def lemmaCoyoIsoK[->[_,_], F[_], A[_[_]]](using
    C: SubcatKHasId[->, F], E: ExofunctorK[Dual[->,*,*], * => *, A]
  ): (([G[_]] =>> ∀[[a] =>> G[a] -> F[a]]) ≈> A) <=> A[F] =
    Iso.unsafe(
      _[F](C.id),
      af => ∀~[[G[_]] =>> ∀[[a] =>> G[a] -> F[a]] => A[G]].fromH([G[_]] => () => (fg: ∀[[a] =>> G[a] -> F[a]]) => E.map(Dual.forall(fg))(af))
    )

  def yoEmbeddingGenericK[-->[_,_], ==>[_,_], F[_], G[_]](using
    C: SubcatKHasId[-->, F], E: ExofunctorK[-->, * => *, [X[_]] =>> ∀[[a] =>> G[a] ==> X[a]]]
  ): ∀~[[X[_]] =>> ∀[[a] =>> F[a] --> X[a]] => ∀[[a] =>> G[a] ==> X[a]]] <=> ∀[[a] =>> G[a] ==> F[a]] =
    lemmaYoIsoK[-->, F, [X[_]] =>> ∀[[a] =>> G[a] ==> X[a]]]

  def coyoEmbeddingGenericK[-->[_,_], ==>[_,_], F[_], G[_]](using
    C: SubcatKHasId[-->, F], E: ExofunctorK[Dual[-->,*,*], * => *, [X[_]] =>> ∀[[a] =>> X[a] ==> G[a]]]
  ): ∀~[[X[_]] =>> ∀[[a] =>> X[a] --> F[a]] => ∀[[a] =>> X[a] ==> G[a]]] <=> ∀[[a] =>> F[a] ==> G[a]] =
    lemmaCoyoIsoK[-->, F, [X[_]] =>> ∀[[a] =>> X[a] ==> G[a]]]

}
