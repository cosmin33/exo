package io.cosmo.exo.categories.instances.isos

import cats.free.{Coyoneda, Yoneda}
import cats.implicits._
import cats.{Contravariant, Functor}
import io.cosmo.exo._
import io.cosmo.exo.categories._
import io.cosmo.exo.categories.functors._
import io.cosmo.exo.evidence.===

trait yoneda {

  def yoIso  [F[_], A] = (f: Functor[F]) => Iso.unsafeT[F[A], Yoneda[F, A]  ](Yoneda(_)(f), _(identity))
  def coyoIso[F[_], A] = (f: Functor[F]) => Iso.unsafeT[F[A], Coyoneda[F, A]](Coyoneda.lift, _.run(f))

  implicit def yonedaIso1  [F[_]: Functor, A]: F[A] <=> Yoneda[F, A]   = yoIso[F, A](Functor[F])
  implicit def coyonedaIso1[F[_]: Functor, A]: F[A] <=> Coyoneda[F, A] = coyoIso[F, A](Functor[F])

  implicit def yonedaFunIso   = ForallK1.of[λ[(f[_],a) => Functor[f] => (f[a] <=> Yoneda[f, a]  )]].from(yoIso)
  implicit def coyonedaFunIso = ForallK1.of[λ[(f[_],a) => Functor[f] => (f[a] <=> Coyoneda[f, a])]].from(coyoIso)

  // indirect equality
  def lmIndirectEquality[A, B]: ∀[λ[x => (A => x) === (B => x)]] <=> (B === A) = ???

  def lemmaYoIsoC[->[_,_], ->#[_], P[_,_], PI, A, F[_]](implicit
    C: Subcat.Aux[->, ->#],
    CCC: Ccc.Aux[->, P, ->#, PI, ->],
    TC1: ->#[A],
    E : Endofunctor.Aux[->, F, ->#]
  ): ∀[λ[x => (A -> x) -> F[x]]] <=> F[A] =
    Iso.unsafeT[∀[λ[x => A -> x -> F[x]]], F[A]](
      f => {
        val a0: A -> A -> F[A] = f.apply[A]
        val ii: A -> A = C.id[A]
        val ss: PI -> P[PI, PI] = CCC.cartesian.coidr[PI]

        //CCC.cartesian.bifunctor.()

        //val aa = CCC.cartesian.associate(a0)
        //val a1 = CCC.uncurry[A, A, F[A]](a0)

        //a1(C.id[A])

        ???
      },
      fa => {
        def dd[x]: A -> x => F[A] -> F[x] = E.map[A, x]

//        def ff[x]: F[A] -> F[x] => P[F[A] -> F[x], F[A]] = CCC.cartesian.&&&(identity, _ => fa)
//        def gg[x]: P[F[A] -> F[x], F[A]] => F[x] = CCC.apply[F[A], F[x]]
        //def trans[x] = dd[x].andThen(ff[x]).andThen(gg[x])



        //def tt[x] =

//        ∀.of[λ[x => (A -> x) => F[x]]].from(trans)

        ???
      }
    )

  def lemmaCoyoIsoC[->[_,_], P[_,_], C1[_], A, F[_]](implicit
    C: Subcat.Aux[->, C1],
    CCC: Ccc.Aux[* => *, P, Trivial.T1, Unit, ->],
    TC1: C1[A],
    E : Exofunctor.Aux[Opp[->]#l, ->, F, C1, C1]
  ): ∀[λ[x => (x -> A) => F[x]]] <=> F[A] =
    Iso.unsafeT[∀[λ[x => (x -> A) => F[x]]], F[A]](
      _.apply[A](C.id[A]),
      fa => {
        def dd[x]: x -> A => F[A] -> F[x] = E.map[A, x]
        def ff[x]: F[A] -> F[x] => P[F[A] -> F[x], F[A]] = CCC.cartesian.&&&(identity, _ => fa)
        def gg[x]: P[F[A] -> F[x], F[A]] => F[x] = CCC.apply[F[A], F[x]]
        def trans[x] = dd[x].andThen(ff[x]).andThen(gg[x])
        ∀.of[λ[x => (x -> A) => F[x]]].from(trans)
      }
    )

  // yoneda lemma
  def lemmaYoIso[A, F[_]: Functor]: ((A => *) ~> F) <=> F[A] =
    Iso.unsafeT[∀[λ[x => (A => x) => F[x]]], F[A]](
      _.apply[A](identity),
      fa => ∀.mk[(A => *) ~> F].from(fa.map)
    )
  def lemmaCoyoIso[A, F[_]: Contravariant]: ((* => A) ~> F) <=> F[A] =
    Iso.unsafeT[∀[λ[x => (x => A) => F[x]]], F[A]](
      _.apply[A](identity),
      fa => ∀.mk[(* => A) ~> F].from(fa.contramap),
    )

  // yoneda embeddings
  def yoEmbedding  [A, B]: ((A => *) ~> (B => *)) <=> (B => A) = lemmaYoIso  [A, B => *]
  def coyoEmbedding[A, B]: ((* => A) ~> (* => B)) <=> (A => B) = lemmaCoyoIso[A, * => B]

  // corolaries (embeddings for isomorphisms)
  def yoCorol1[A, B]: ((* => A) <~> (* => B)) <=> (A <=> B) =
    Iso.unsafeT[∀[λ[x => (x => A) <=> (x => B)]], A <=> B](
      fa => Iso.unsafeT(fa.apply[A].to(identity), fa.apply[B].from(identity)),
      ab => {
        val fn1: (* => A) ~> (* => B) = coyoEmbedding[A, B].from(ab.to)
        val fn2: (* => B) ~> (* => A) = coyoEmbedding[B, A].from(ab.from)
        ∀.mk[(* => A) <~> (* => B)].fromH(t => Iso.unsafeT(fn1[t.T], fn2[t.T]))
      }
    )
  def yoCorol2[A, B]: ((A => *) <~> (B => *)) <=> (B <=> A) =
    Iso.unsafeT[∀[λ[x => (A => x) <=> (B => x)]], B <=> A](
      fa => Iso.unsafeT(fa.apply[A].to(identity), fa.apply[B].from(identity)),
      ba => {
        val fn1: (A => *) ~> (B => *) = yoEmbedding[A, B].from(ba.to)
        val fn2: (B => *) ~> (A => *) = yoEmbedding[B, A].from(ba.from)
        ∀.mk[(A => *) <~> (B => *)].fromH(t => Iso.unsafeT(fn1[t.T], fn2[t.T]))
      }
    )

  //def yonedaDoubleEmbed[A, B]: (A => B) <=> ∀~[λ[f[_] => f[A] => f[B]]] = ???


}

object yoneda extends yoneda
