package io.cosmo.exo

import io.cosmo.exo.evidence.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax._

val Forall: ForallModule = ForallImpl
val ∀ : Forall.type = Forall
type Forall[F[_]] = Forall.Forall[F]
type ∀[F[_]] = Forall.Forall[F]

/** universal quantifier, taken from scalaz 8 */
sealed trait ForallModule {
  type Forall[F[_]]
  type ∀[F[_]] = Forall[F]

  trait Prototype[F[_]]:
    def apply[X]: F[X]
    final def make: ∀[F] = from(this)

  def specialize[F[_], A](v: ∀[F]): F[A]
  def instantiation[F[_], A]: ∀[F] <~< F[A]
  def vacuous[A]: A <~< ∀[[α] =>> A]
  def monotonicity[F[_], G[_]](ev: ∀[[α] =>> F[α] <~< G[α]]): ∀[F] <~< ∀[G]
  def from[F[_]](p: Prototype[F]): ∀[F]
  def of[F[_]]: MkForall[F]
  def mk[X](implicit u: Unapply[X]): MkForall[u.F] = of[u.F]
  def const[A](a: A): ∀[[α] =>> A]

  trait MkForall[F[_]] extends Any:
    type T
    def from(ft: F[T]): ∀[F]
    def apply(ft: F[T]): ∀[F] = from(ft)
    def fromH(ft: [T] => () => F[T]): Forall[F] = from(ft[T]())

  trait Unapply[X]:
    type F[_]

  object Unapply:
    type Aux[X, F0[_]] = Unapply[X] { type F[a] = F0[a] }
    given [G[_]]: Unapply.Aux[∀[G], G] = new Unapply[∀[G]] { type F[A] = G[A] }
}

object ForallModule extends ForallFunctions:
  def isoCanonic[F[_]]: ∀[F] <=> ([A] => () => F[A]) =
    Iso.unsafe[Function, ∀[F], [A] => () => F[A]](
      faf => [A] => () => faf[A],
      f => ∀.of[F].fromH([T] => () => f[T]())
    )
  extension[F[_]] (f: ∀[F])
    def apply[A]: F[A] = ∀.specialize(f)
    def of[A]: F[A] = apply[A]
    def lift[G[_]]: ∀[[α] =>> F[G[α]]] = ∀.of[[α] =>> F[G[α]]].from(of)
  extension[F[_], G[_]] (fg: F ~> G)
    def run[A](fa: F[A]): G[A] = fg[A](fa)
    def forall: ∀[[o] =>> F[o] => G[o]] = ∀.of[[a] =>> F[a] => G[a]].from(run)
    def $(f: ∀[F]): ∀[G] = ∀.of[G].from(run(f.apply))
    def andThen[H[_]](gh: G ~> H): F ~> H = ∀.mk[F ~> H].fromH([T] => () => fg[T].andThen(gh[T]))
    def compose[E[_]](ef: E ~> F): E ~> G = ∀.mk[E ~> G].fromH([T] => () => fg[T].compose(ef[T]))
  extension[->[_,_], F[_], G[_]](iso: IsoK[->, F, G])
    def to  : ∀[[a] =>> F[a] -> G[a]] = ∀.of[[a] =>> F[a] -> G[a]].fromH([T] => () => iso[T].to)
    def from: ∀[[a] =>> G[a] -> F[a]] = ∀.of[[a] =>> G[a] -> F[a]].fromH([T] => () => iso[T].from)
    def flip: IsoK[->, G, F] = ∀.of[[a] =>> Iso[->, G[a], F[a]]].fromH([T] => () => iso[T].flip)
    def andThenIso[H[_]](iso2: IsoK[->, G, H]): IsoK[->, F, H] =
      ∀.mk[IsoK[->, F, H]].fromH([T] => () => iso[T].andThen(iso2[T]))

private[exo] object ForallImpl extends ForallModule:
  type Forall[F[_]] = F[Any]
  def specialize[F[_], A](f: ∀[F]): F[A] = f.asInstanceOf[F[A]]
  def instantiation[F[_], A]: ∀[F] <~< F[A] = As.refl[Any].asInstanceOf[∀[F] <~< F[A]]
  def vacuous[A]: A <~< ∀[[α] =>> A] = As.refl[A]
  def monotonicity[F[_], G[_]](ev: ∀[[α] =>> F[α] <~< G[α]]): ∀[F] <~< ∀[G] = As.refl[Any].asInstanceOf[∀[F] <~< ∀[G]]
  def from[F[_]](p: Prototype[F]): ∀[F] = p[Any]
  def of[F[_]]: MkForall[F] = new MkForallImpl[F]
  def const[A](a: A): ∀[[α] =>> A] = of[[α] =>> A].from(a)

private[exo] final class MkForallImpl[F[_]](val dummy: Boolean = false) extends AnyVal with ForallImpl.MkForall[F]:
  type T = Any
  def from(ft: F[T]): ForallImpl.∀[F] = ft

trait ForallFunctions {

  // https://nokyotsu.com/qscripts/2014/07/distribution-of-quantifiers-over-logic-connectives.html
  ////////////////////////
  def isoDistribFn[A, F[_]]: ∀[[x] =>> A => F[x]] <=> (A => ∀[F]) =
    Iso.unsafe(
      faf => a => ∀.of[F].fromH([T] => () => faf.apply[T].apply(a)),
      aff => ∀.of[[x] =>> A => F[x]].from(a => aff(a).apply)
    )

  def fnLowerFunk[F[_], G[_]](fg: F ~> G): ∀[F] => ∀[G] = fg.$(_)

  def fnLowerIsok[F[_], G[_]](fg: F <~> G): ∀[F] <=> ∀[G] = Iso.unsafe(fg.to.$(_), fg.from.$(_))

  //////////////////////////// ⨂

  /** ∀ distributes over the product of a Cartesian */
  def fnDistribCartesianTo[F[_], G[_], ⨂[_, _]](using
    cc: Cartesian.AuxT[* => *, ⨂, Trivial]
  ): ∀[[x] =>> F[x] ⨂ G[x]] => (∀[F] ⨂ ∀[G]) =
    cc.&&&(f => ∀.of[F].fromH([T] => () => cc.fst.apply(f[T])), f => ∀.of[G].fromH([T] => () => cc.snd.apply(f[T])))

  def fnDistribCartesianFrom[F[_], G[_], ⨂[_, _]](implicit
    cc: Cartesian[* => *, ⨂]
  ): (∀[F] ⨂ ∀[G]) => ∀[[x] =>> F[x] ⨂ G[x]] =
    fg => ∀.of[[x] =>> F[x] ⨂ G[x]].fromH([T] => () => cc.bifunctor.bimap[∀[F], F[T], ∀[G], G[T]](_[T], _[T])(fg))

  def isoDistributeCartesian[F[_], G[_], ⨂[_, _]](implicit
    cc: Cartesian.AuxT[* => *, ⨂, Trivial]
  ): ∀[[x] =>> F[x] ⨂ G[x]] <=> (∀[F] ⨂ ∀[G]) = Iso.unsafe(fnDistribCartesianTo, fnDistribCartesianFrom)

  // these are not really needed because they are a specific type (for Tuple2) of those above
  def fnDistribTupleTo[F[_], G[_]]: ∀[[x] =>> (F[x], G[x])] => (∀[F], ∀[G]) =
    f => (∀.of[F].fromH([T] => () => f.apply[T]._1), ∀.of[G].fromH([T] => () => f.apply[T]._2))

  def fnDistribTupleFrom[F[_], G[_]]: (∀[F], ∀[G]) => ∀[[x] =>> (F[x], G[x])] =
    (f, g) => ∀.of[[x] =>> (F[x], G[x])].fromH([T] => () => (f[T], g[T]))

  def isoDistribTuple[F[_], G[_]]: ∀[[x] =>> (F[x], G[x])] <=> (∀[F], ∀[G]) =
    Iso.unsafe(fnDistribTupleTo, fnDistribTupleFrom(_, _))

  //////////////////////// ⨁

  /** ∀ distributes over the coproduct of a Cocartesian (one way only) */
  def fnDistributeCocartesian[F[_], G[_], ⨁[_, _]](implicit
    cc: Cocartesian.AuxT[* => *, ⨁, Trivial]
  ): (∀[F] ⨁ ∀[G]) => ∀[[x] =>> F[x] ⨁ G[x]] = coproduct =>
    {
      def f1[x]: ∀[F] => F[x] ⨁ G[x] = f => cc.fst[F[x], G[x]].apply(f[x])
      def f2[x]: ∀[G] => F[x] ⨁ G[x] = f => cc.snd[F[x], G[x]].apply(f[x])
      ∀.of[[x] =>> F[x] ⨁ G[x]].fromH([T] => () => cc.&&&(Dual(f1[T]), Dual(f2[T]))(coproduct))
    }

  // these are not really needed because they are a specific type (for \/) of those above
  def fnDistribDisj[F[_], G[_]]: (∀[F] \/ ∀[G]) => ∀[[x] =>> F[x] \/ G[x]] =
    e => ∀.of[[x] =>> F[x] \/ G[x]].fromH([T] => () => e.fold(_.apply[T].left, _.apply[T].right))

  ////////////////////////

  /** ∀ is commutative */
  def commute1[F[_, _]]: ∀[[a] =>> ∀[F[a, *]]] => ∀[[b] =>> ∀[F[*, b]]] =
    ab => ∀.of[[b] =>> ∀[F[*, b]]].fromH([b] => () => ∀.of[F[*, b]].fromH([a] => () => ab[a][b]))

  def commute2[F[_, _]]: ∀[[b] =>> ∀[F[*, b]]] => ∀[[a] =>> ∀[F[a, *]]] =
    ab => ∀.of[[a] =>> ∀[F[a, _]]].fromH([a] => () => ∀.of[F[a, _]].fromH([b] => () => ab[b][a]))

  def isoCommute[F[_, _]]: ∀[[a] =>> ∀[[b] =>> F[a, b]]] <=> ∀[[b] =>> ∀[[a] =>> F[a, b]]] =
    Iso.unsafe(commute1[F], commute2[F])

  def isoLift2[F[_,_]]: ∀[[a] =>> ∀[[b] =>> F[a, b]]] <=> ∀∀[F] =
    Iso.unsafe(
      ab => ∀∀.of[F].fromH([A, B] => () => ab[A][B]),
      ff => ∀.of[[a] =>> ∀[F[a, *]]].fromH([A] => () => ∀.of[F[A, *]].fromH([B] => () => ff[A, B]))
    )

  ////////////////////////
}
