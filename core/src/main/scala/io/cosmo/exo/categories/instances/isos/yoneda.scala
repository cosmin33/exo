package io.cosmo.exo.categories.instances.isos

import cats.free.{Coyoneda, Yoneda}
import cats.implicits._
import cats.{Contravariant, Functor}
import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.evidence.===
import io.cosmo.exo.categories.conversions.CatsInstances._

trait yoneda {

  implicit def yonedaIso1  [F[_]: Functor, A]: F[A] <=> Yoneda[F, A]   = Iso.unsafe(Yoneda(_), _(identity))
  implicit def coyonedaIso1[F[_]: Functor, A]: F[A] <=> Coyoneda[F, A] = Iso.unsafe(Coyoneda.lift, _.run)

  // indirect equality
  def lmIndirectEquality[A, B]: ∀[λ[x => (A => x) === (B => x)]] <=> (B === A) = ???

  /** yoneda lemma covariant (generic category) */
  def lemmaYoIsoC[->[_,_], ->#[_], A, F[_]](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exofunctor[->, * => *, F]
  ): ∀[λ[x => (A -> x) => F[x]]] <=> F[A] =
    Iso.unsafe(_[A](C.id), fa => ∀.of[λ[x => A -> x => F[x]]].from(E.map(_)(fa)))
  /** yoneda lemma contravariant (generic category) */
  def lemmaCoyoIsoC[->[_,_], ->#[_], A, F[_]](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exofunctor[Opp[->]#l, * => *, F]
  ): ∀[λ[x => (x -> A) => F[x]]] <=> F[A] =
    Iso.unsafe(_.apply[A](C.id[A]), fa => ∀.of[λ[x => x -> A => F[x]]].from(E.map(_)(fa)))

  def yoEmbeddingC[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exofunctor[->, * => *, B -> *]
  ): ∀[λ[x => (A -> x) => (B -> x)]] <=> (B -> A) = lemmaYoIsoC[->, ->#, A, B -> *]
  def coyoEmbeddingC[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exofunctor[Opp[->]#l, * => *, * -> B]
  ): ∀[λ[x => (x -> A) => (x -> B)]] <=> (A -> B) = lemmaCoyoIsoC[->, ->#, A, * -> B]

  /** yoneda lemma covariant for Function1 */
//  def lemmaYoIso1[A, F[_]: Exofunctor.CovF]: ((A => *) ~> F) <=> F[A] =
//    lemmaYoIsoC
  def lemmaYoIso[A, F[_]: Functor]: ((A => *) ~> F) <=> F[A] =
    Iso.unsafe(_[A](identity), fa => ∀.mk[(A => *) ~> F].from(fa.map))
  /** yoneda lemma contravariant for Function1 */
//  def lemmaCoyoIso1[A, F[_]: Exofunctor.ConF]: ((* => A) ~> F) <=> F[A] =
//    lemmaCoyoIsoC[* => *, Trivial.T1, A, F]
  def lemmaCoyoIso[A, F[_]: Contravariant]: ((* => A) ~> F) <=> F[A] =
    Iso.unsafe(_[A](identity), fa => ∀.mk[(* => A) ~> F].from(fa.contramap))

  /** yoneda embedding (covariant) */
  def yoEmbedding  [A, B]: ((A => *) ~> (B => *)) <=> (B => A) = lemmaYoIso  [A, B => *]
  /** yoneda embedding (contravariant) */
  def coyoEmbedding[A, B]: ((* => A) ~> (* => B)) <=> (A => B) = lemmaCoyoIso[A, * => B]

  /** Yoneda embedding corolary 1 */
  def yoCorol1[A, B]: ((* => A) <~> (* => B)) <=> (A <=> B) =
    Iso.unsafe(
      fa => Iso.unsafe(fa.apply[A].to(identity), fa.apply[B].from(identity)),
      ab => {
        val fn1: (* => A) ~> (* => B) = coyoEmbedding[A, B].from(ab.to)
        val fn2: (* => B) ~> (* => A) = coyoEmbedding[B, A].from(ab.from)
        ∀.mk[(* => A) <~> (* => B)].fromH(t => Iso.unsafe(fn1[t.T], fn2[t.T]))
      }
    )
  /** yoneda embedding corolary 2 */
  def yoCorol2[A, B]: ((A => *) <~> (B => *)) <=> (B <=> A) =
    Iso.unsafe(
      fa => Iso.unsafe(fa.apply[A].to(identity), fa.apply[B].from(identity)),
      ba => {
        val fn1: (A => *) ~> (B => *) = yoEmbedding[A, B].from(ba.to)
        val fn2: (B => *) ~> (A => *) = yoEmbedding[B, A].from(ba.from)
        ∀.mk[(A => *) <~> (B => *)].fromH(t => Iso.unsafe(fn1[t.T], fn2[t.T]))
      }
    )

  //def yonedaDoubleEmbed[A, B]: (A => B) <=> ∀~[λ[f[_] => f[A] => f[B]]] = ???


}

object yoneda extends yoneda
