package io.cosmo.exo.categories.instances.isos

import cats.free.{Coyoneda, Yoneda}
import cats.implicits._
import cats.{Contravariant, Functor, Id}
import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.evidence.{<~<, ===}
import io.cosmo.exo.categories.conversions.CatsInstances._
import io.cosmo.exo.evidence.variance.IsCovariant

trait yoneda {

  implicit def yonedaIso1  [F[_]: Functor, A]: F[A] <=> Yoneda[F, A]   = Iso.unsafe(Yoneda(_), _(identity))
  implicit def coyonedaIso1[F[_]: Functor, A]: F[A] <=> Coyoneda[F, A] = Iso.unsafe(Coyoneda.lift, _.run)

  // indirect equality
//  def lmIndirectEquality[A, B]: ∀[λ[x => (A === x) => (B === x)]] <=> (B === A) = yoCorol1C[===, Trivial.T1, A, B]

  /** yoneda lemma covariant (generic category) */
  def lemmaYoIsoCov[->[_,_], ->#[_], A, F[_]](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Cov[->, F]
  ): ∀[λ[x => (A -> x) => F[x]]] <=> F[A] =
    Iso.unsafe(_[A](C.id), fa => ∀.of[λ[x => A -> x => F[x]]].from(E.map(_)(fa)))
  // trial:
  def lemmaYoIsoCov1[->[_,_], ->#[_], A, F[_]](implicit
    C: Subcat.Aux[->, ->#],
    tc: ->#[A],
    ccc: Ccc.AuxPH[->, Tuple2, ->],
    E: Exo[->, ->, F],
  ): ∀[λ[x => A -> x -> F[x]]] <=> F[A] = {
    //def brr[x] = ccc.
    val x1: A -> A -> F[A] = ???
    val x2: A -> A = C.id[A]
    def ee[B]: A -> B => F[A] -> F[B] = E.map[A, B]


    ???
    // magarie, nu se poate
  }
  /** yoneda lemma contravariant (generic category) */
  def lemmaYoIsoCon[->[_,_], ->#[_], A, F[_]](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Con[->, F]
  ): ∀[λ[x => (x -> A) => F[x]]] <=> F[A] =
    Iso.unsafe(_[A](C.id[A]), fa => ∀.of[λ[x => x -> A => F[x]]].from(xa => E.map(Dual(xa))(fa)))

  def yoEmbeddingC[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Cov[->, B -> *]
  ): ((A -> *) ~> (B -> *)) <=> (B -> A) = lemmaYoIsoCov[->, ->#, A, B -> *]
  def coyoEmbeddingC[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E : Exo.Con[->, * -> B]
  ): ((* -> A) ~> (* -> B)) <=> (A -> B) = lemmaYoIsoCon[->, ->#, A, * -> B]

  // yoneda cre'ca-i stricata, altfel ar trebui sa mearga asta:
  def exIndirectInequality[A, B]: ((A <~< *) ~> (B <~< *)) <=> (B <~< A) = {
    implicitly[IsCovariant[B <~< *]]
    implicitly[Exofunctor[<~<, <~<, B <~< *]]
    //implicitly[Exofunctor[<~<, * => *, B <~< *]]
    //val r2: <=>[(A <~< *) ~> (B <~< *), B <~< A] = yoEmbeddingC[<~<, Trivial.T1, A, B]
    //val rr: <=>[∀[λ[x => (A <~< x) <~< (B <~< x)]], B <~< A] = yoEmbeddingD[<~<, Trivial.T1, A, B]
    ???
  }

  def yoEmbedTo[->[_,_], A, B, ->#[_]](fa: (A -> *) ~> (B -> *))(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Cov[->, B -> *]
  ): B -> A = yoEmbeddingC.to(fa)
  def coyoEmbedTo[->[_,_], A, B, ->#[_]](fa: (* -> A) ~> (* -> B))(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Con[->, * -> B]
  ): A -> B = coyoEmbeddingC.to(fa)
  def yoEmbedFrom[->[_,_], A, B, ->#[_]](ba: B -> A)(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Cov[->, B -> *]
  ): (A -> *) ~> (B -> *) = yoEmbeddingC.from(ba)
  def coyoEmbedFrom[->[_,_], A, B, ->#[_]](ab: A -> B)(implicit
    C: Subcat.Aux[->, ->#], tc: ->#[A], E: Exo.Con[->, * -> B]
  ): (* -> A) ~> (* -> B) = coyoEmbeddingC.from(ab)

  def yoDoubleEmbed[->[_,_], ->#[_], A, B](implicit
    cat: Subcat.Aux[->, ->#],
    F: Endofunctor[->, λ[a => a]]
  ): (A -> B) <=> ∀~[λ[f[_] => Endofunctor[->, f] => f[A] -> f[B]]] = {
    Iso.unsafe(
      ab => ∀~.of[λ[f[_] => Endofunctor[->, f] => f[A] -> f[B]]].from(_.map(ab)),
      fa => fa.apply[λ[a => a]](F)
    )
  }

  def yoCorol1C[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tca: ->#[A], tcb: ->#[B],
    Ea: Exo.Cov[->, A -> *],
    Eb: Exo.Cov[->, B -> *],
  ): ((A -> *) <~> (B -> *)) <=> Iso[->, B, A] =
      Iso.unsafe(
        fa => Iso.unsafe(fa.apply[A].to(C.id[A]), fa.apply[B].from(C.id[B])),
        ba => <~>.unsafe[A -> *, B -> *](yoEmbedFrom(ba.to), yoEmbedFrom(ba.from))
      )

  def coyoCorol1C[->[_,_], ->#[_], A, B](implicit
    C: Subcat.Aux[->, ->#], tca: ->#[A], tcb: ->#[B],
    Ea: Exo.Con[->, * -> A],
    Eb: Exo.Con[->, * -> B],
  ): ((* -> A) <~> (* -> B)) <=> Iso[->, A, B] =
    Iso.unsafe(
      i => Iso.unsafe(i.of[A].to(C.id[A]), i.of[B].from(C.id[B])),
      i => <~>.unsafe[* -> A, * -> B](coyoEmbedFrom(i.to), coyoEmbedFrom(i.from))
    )

  /** yoneda lemma covariant for Function1 */
  def lemmaYoIso[A, F[_]: Exofunctor.CovF]: ((A => *) ~> F) <=> F[A] = lemmaYoIsoCov
  /** yoneda lemma contravariant for Function1 */
  def lemmaCoyoIso[A, F[_]: Exofunctor.ConF]: ((* => A) ~> F) <=> F[A] = lemmaYoIsoCon
  /** yoneda embedding (covariant) */
  def yoEmbedding  [A, B]: ((A => *) ~> (B => *)) <=> (B => A) = lemmaYoIso  [A, B => *]
  /** yoneda embedding (contravariant) */
  def coyoEmbedding[A, B]: ((* => A) ~> (* => B)) <=> (A => B) = lemmaCoyoIso[A, * => B]
  /** yoneda embedding corolary 1 */
  def yoCorol1[A, B]: ((A => *) <~> (B => *)) <=> (B <=> A) = yoCorol1C
  /** coyoneda embedding corolary 1 */
  def coyoCorol1[A, B]: ((* => A) <~> (* => B)) <=> (A <=> B) = coyoCorol1C

  //def yoCorol2[A, B]: <=>[(A <~< *) <~> (B <~< *), Iso[<~<, B, A]] = yoCorol1C[<~<, Trivial.T1, A, B]

  //def yonedaDoubleEmbed[A, B]: (A => B) <=> ∀~[λ[f[_] => Functor[f] => f[A] => f[B]]] = ???


}

object yoneda extends yoneda
