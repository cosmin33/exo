package io.cosmo.exo

import io.cosmo.exo.categories.*
import io.cosmo.exo.evidence.*
import io.cosmo.exo.functors.*

object yoneda {
  /** yoneda lemma for covariant functor */
  def lemmaYoIso[->[_,_], A, F[_]](using
    C: SubcatHasId[->, A], E: Exo.Cov[->, F]
  ): (->[A,*] ~> F) <=> F[A] = Iso.unsafe(_[A](C.id), fa => ∀.of[[o] =>> A -> o => F[o]].from(E.map(_)(fa)))
  /** yoneda lemma for contravariant functor */
  def lemmaCoyoIso[->[_,_], A, F[_]](using
    C: SubcatHasId[->, A], E: Exo.Con[->, F]
  ): (->[*,A] ~> F) <=> F[A] =
    Iso.unsafe(_[A](C.id), fa => ∀.of[[o] =>> o -> A => F[o]].from(xa => E.map(Dual(xa))(fa)))

  def yoEmbeddingGeneric[-->[_,_], ==>[_,_], A, B](using
    C: SubcatHasId[-->, A], F: Exo.Cov[-->, [o] =>> B ==> o]
  ): (-->[A,*] ~> ==>[B,*]) <=> (B ==> A) = lemmaYoIso[-->, A, [o] =>> B ==> o]

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
  private def isoIndirectLeibni_[A, B]: ∀[[a] =>> (A === a) <=> (B === a)] <=> (A === B) = {
    val ee: (===[A,*] <~> ===[B,*]) <=> Iso[===, B, A] = yoCorollary[===, A, B]
    
    //yoCorollary[===, A, B] andThen Iso.isoGroupoid[===, B, A].flip andThen Iso.isoGroupoidFlip
    ???
  }
  //       coyoCorollary[===, A, B].chain[B === A].chain[A === B] // strange compile error for this one but it should work, I think it's a scala bug ?!?!

//  private def isoIndirectLiskov [A, B]: ((A <~< *)  ~> (B <~< *)) <=> (B <~< A) = yoEmbedding
//  private def isoIndirectLeibniz[A, B]: ((A === *)  ~> (B === *)) <=> (A === B) = yoEmbedding[===, A, B] andThen Iso.isoGroupoidFlip
//  private def isoIndirectLeibni_[A, B]: ((A === *) <~> (B === *)) <=> (A === B) =
//    yoCorol1[===, A, B] andThen Iso.isoGroupoid[===, B, A].flip andThen Iso.isoGroupoidFlip
//  //       yoCorol1Cov[===, A, B].chain[B === A].chain[A === B] // strange compile error for this one but it should work, I think it's a scala bug ?!?!
//  // TODO: investigate why the above doesn't work

}
