package io.cosmo.exo.functors

import io.cosmo.exo.*
import io.cosmo.exo.categories.*
import io.cosmo.exo.syntax.*
import io.cosmo.exo.internal.any.*
import io.cosmo.exo.internal.*

trait Exobifunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]]:
  def bimap[A, X, B, Y](left: A ==> X, right: B --> Y): ⊙[A, B] >-> ⊙[X, Y]

  def leftMap [A, B, Z](fn: A ==> Z)(using C: SubcatHasId[-->, B]): ⊙[A, B] >-> ⊙[Z, B] = bimap(fn, C.id)
  def rightMap[A, B, Z](fn: B --> Z)(using C: SubcatHasId[==>, A]): ⊙[A, B] >-> ⊙[A, Z] = bimap(C.id, fn)

  def leftFunctor [X](using C: SubcatHasId[-->, X]): Exo[==>, >->, ⊙[*, X]] =
    Exo.unsafe[==>, >->, ⊙[*, X]]([a, b] => (fn: a ==> b) => leftMap(fn))
  def rightFunctor[X](using C: SubcatHasId[==>, X]): Exo[-->, >->, ⊙[X, *]] =
    Exo.unsafe[-->, >->, ⊙[X, *]]([a, b] => (fn: a --> b) => rightMap(fn))

  def leftForall [T[_]](using C: Subcat.Aux[-->, T]): T ~> ([x] =>> Exo[==>, >->, ⊙[*, x]]) =
    ~>([A] => (ta: T[A]) => leftFunctor(using SubcatHasId.from(using C, ta)))
  def rightForall[T[_]](using C: Subcat.Aux[==>, T]): T ~> ([x] =>> Exo[-->, >->, ⊙[x, *]]) =
    ~>([A] => (ta: T[A]) => rightFunctor(using SubcatHasId.from(using C, ta)))

object Exobifunctor extends ExobifunctorInstances
  with ExobifunctorImplicits
  with DualBifunctorInstances 
  with EvidenceCatBifunctorInstances
  with ProdcatBifunctorInstances:

  def apply[=>:[_,_], ->:[_,_], ~>:[_,_], ⊙[_,_]](using bi: Exobifunctor[=>:, ->:, ~>:, ⊙]): Exobifunctor[=>:, ->:, ~>:, ⊙] = bi

  def fromFaFunctors[==>[_,_], -->[_,_], >->[_,_]: Semicategory, Bi[_,_]](
   L: ∀[[a] =>> Exo[==>, >->, Bi[*, a]]],
   R: ∀[[a] =>> Exo[-->, >->, Bi[a, *]]]
 ): Exobifunctor[==>, -->, >->, Bi] =
    new Exobifunctor[==>, -->, >->, Bi]:
      def bimap[A, X, B, Y](l: A ==> X, r: B --> Y): Bi[A, B] >-> Bi[X, Y] = L[B].map(l) >>> R[X].map(r)
      override def leftMap [A, B, Z](fn:  A ==> Z)(using C:  SubcatHasId[-->, B]) = L[B].map(fn)
      override def rightMap[A, B, Z](fn:  B --> Z)(using C:  SubcatHasId[==>, A]) = R[A].map(fn)

  extension[==>[_,_], >->[_,_], F[_,_]](self: Exobifunctor[==>, ==>, >->, F])
    def compose[G[_,_]](using G: Endobifunctor[==>, G]): Exobifunctor[==>, ==>, >->, [α, β] =>> F[G[α, β], G[α, β]]] =
      new Exobifunctor[==>, ==>, >->, [α, β] =>> F[G[α, β], G[α, β]]]:
        def bimap[A, X, B, Y](l: A ==> X, r: B ==> Y) = G.bimap(l, r) |> (i => self.bimap(i, i))
  extension[==>[_,_], -->[_,_], >->[_,_], P[_,_]](self: Exoprofunctor[==>, -->, >->, P])
    def promap[A, X, B, Y](l: X ==> A, r: B --> Y): P[A, B] >-> P[X, Y] = self.bimap(Dual(l), r)

  def dual[->[_,_], Bi[_,_]](F: Endobifunctor[->, Bi]): Endobifunctor[Dual[->,*,*], Bi] =
    new Endobifunctor[Dual[->,*,*], Bi]:
      def bimap[A, X, B, Y](l: Dual[->, A, X], r: Dual[->, B, Y]): Dual[->, Bi[A, B], Bi[X, Y]] = Dual(F.bimap(l, r))

  def opp[->[_,_], Bi[_,_]](F: Endobifunctor[->, Bi]): Endobifunctor[Opp[->], Bi] =
    Dual.leibniz[->].flip.subst[[f[_,_]] =>> Endobifunctor[f, Bi]](dual(F))

end Exobifunctor

trait ExobifunctorInstances:
  given semicatToExobifunctor[->[_,_]](using s: Semicategory[->]): Exobifunctor[Dual[->,*,*], ->, Function, ->] =
    new Exobifunctor[Dual[->,*,*], ->, * => *, ->]:
      def bimap[A, X, B, Y](left: Dual[->, A, X], right: B -> Y): (A -> B) => (X -> Y) = left.toFn >>> _ >>> right
  given profunctor[->[_,_]: Semicategory]: Exobifunctor[Dual[->,*,*], ->, * => *, ->] =
    new Exobifunctor[Dual[->,*,*], ->, * => *, ->]:
      def bimap[A, X, B, Y](left: Dual[->, A, X], right: B -> Y): A -> B => (X -> Y) = f => left.toFn >>> f >>> right
  given tuple2: EndobifunctorF[Tuple2] =
    new Endobifunctor[* => *, Tuple2]:
      def bimap[A, X, B, Y](l: A => X, r: B => Y): ((A, B)) => (X, Y) = (a, b) => (l(a), r(b))
  given either: EndobifunctorF[Either] =
    new Endobifunctor[* => *, Either]:
      def bimap[A, X, B, Y](l: A => X, r: B => Y): Either[A, B] => Either[X, Y] = _.fold(l(_).asLeft, r(_).asRight)
end ExobifunctorInstances

trait ExobifunctorImplicits:
  // Functor instances
  given cofunctorArrow1[-->[_,_], >->[_,_], ⊙[_,_]]: ContravariantK2[[f[_,_]] =>> Exobifunctor[f, -->, >->, ⊙]] =
    new ContravariantK2.Proto[[f[_,_]] =>> Exobifunctor[f, -->, >->, ⊙]]:
      def comap[F[_, _], G[_, _]](f: G ~~> F): Exobifunctor[F, -->, >->, ⊙] => Exobifunctor[G, -->, >->, ⊙] =
        F => new Exobifunctor[G, -->, >->, ⊙]:
          def bimap[A, X, B, Y](l: G[A, X], r: B --> Y): A ⊙ B >-> (X ⊙ Y) = F.bimap(f.apply(l), r)
  given cofunctorArrow2[==>[_,_], >->[_,_], ⊙[_,_]]: ContravariantK2[[f[_,_]] =>> Exobifunctor[==>, f, >->, ⊙]] =
    new ContravariantK2.Proto[[f[_,_]] =>> Exobifunctor[==>, f, >->, ⊙]]:
      def comap[F[_, _], G[_, _]](f: G ~~> F): Exobifunctor[==>, F, >->, ⊙] => Exobifunctor[==>, G, >->, ⊙] =
        F => new Exobifunctor[==>, G, >->, ⊙]:
          def bimap[A, X, B, Y](l: A ==> X, r: G[B, Y]): A ⊙ B >-> (X ⊙ Y) = F.bimap(l, f.apply(r))
  given functorArrow3[==>[_,_], -->[_,_], ⊙[_,_]]: FunctorK2[[f[_,_]] =>> Exobifunctor[==>, -->, f, ⊙]] =
    new FunctorK2[[f[_,_]] =>> Exobifunctor[==>, -->, f, ⊙]]:
      def map[F[_,_], G[_,_]](f: F ~~> G): Exobifunctor[==>, -->, F, ⊙] => Exobifunctor[==>, -->, G, ⊙] =
        F => new Exobifunctor[==>, -->, G, ⊙]:
          def bimap[A, X, B, Y](l: A ==> X, r: B --> Y): G[A ⊙ B, X ⊙ Y] = f.apply(F.bimap(l, r))
  given cofunctorEndoArrow[>->[_,_], ⊙[_,_]]: ContravariantK2[[f[_,_]] =>> Exobifunctor[f, f, >->, ⊙]] =
    new ContravariantK2.Proto[[f[_,_]] =>> Exobifunctor[f, f, >->, ⊙]]:
      def comap[F[_,_], G[_,_]](f: G ~~> F): Exobifunctor[F, F, >->, ⊙] => Exobifunctor[G, G, >->, ⊙] =
        F => new Exobifunctor[G, G, >->, ⊙]:
          def bimap[A, X, B, Y](l: G[A, X], r: G[B, Y]): A ⊙ B >-> (X ⊙ Y) = F.bimap(f.apply(l), f.apply(r))
  given isofunctorEndoArrow[⊙[_,_]]: IsofunctorK2[[f[_,_]] =>> Exobifunctor[f, f, f, ⊙]] =
    new IsofunctorK2.Proto[[f[_,_]] =>> Exobifunctor[f, f, f, ⊙]]:
      def isomap[F[_,_], G[_,_]](i: F <~~> G): Exobifunctor[F, F, F, ⊙] => Exobifunctor[G, G, G, ⊙] =
        F => new Exobifunctor[G, G, G, ⊙]:
          def bimap[A, X, B, Y](l: G[A, X], r: G[B, Y]): G[A ⊙ B, X ⊙ Y] =
            i.apply.to(F.bimap(i.apply.from(l), i.apply.from(r)))
  given isofunctorFunctor[==>[_,_], -->[_,_], >->[_,_], >=>[_,_]](using P: Exoprofunctor[>=>, >=>, * => *, >->])
  : ExofunctorK2[Iso[>=>,*,*], * => *, [f[_,_]] =>> Exobifunctor[==>, -->, >->, f]] =
    new ExofunctorK2[Iso[>=>,*,*], * => *, [f[_,_]] =>> Exobifunctor[==>, -->, >->, f]]:
      def map[F[_,_], G[_,_]](i: ∀∀[[a, b] =>> Iso[>=>, F[a, b], G[a, b]]])
      : Exobifunctor[==>, -->, >->, F] => Exobifunctor[==>, -->, >->, G] =
        F => new Exobifunctor[==>, -->, >->, G]:
          def bimap[A, X, B, Y](l: A ==> X, r: B --> Y): G[A, B] >-> G[X, Y] =
            P.bimap(i.apply.from.dual, i.apply.to)(F.bimap(l, r))
  // Lax monoidal functor instances
  given laxArrow1[-->[_,_], >->[_,_], ⊙[_,_]]: LaxSemigroupalK2.Aux[Either, * => *, (*,*), Trivial, [f[_,_]] =>> Exobifunctor[f, -->, >->, ⊙]] =
    new LaxSemigroupalK2.Proto[Either, * => *, (*,*), Trivial, [f[_,_]] =>> Exobifunctor[f, -->, >->, ⊙]]:
      def A: Associative.Aux[Function, Tuple2, Trivial] = summon
      def product[F[_,_], G[_,_]]: ((Exobifunctor[F, -->, >->, ⊙], Exobifunctor[G, -->, >->, ⊙])) => Exobifunctor[[a, b] =>> Either[F[a, b], G[a, b]], -->, >->, ⊙] =
        P => new Exobifunctor[[a, b] =>> Either[F[a, b], G[a, b]], -->, >->, ⊙]:
          def bimap[A, X, B, Y](l: Either[F[A, X], G[A, X]], r: B --> Y): A ⊙ B >-> (X ⊙ Y) =
            l.fold(P._1.bimap(_, r), P._2.bimap(_, r))
  given laxArrow2[==>[_,_], >->[_,_], ⊙[_,_]]: LaxSemigroupalK2.Aux[Either, * => *, (*,*), Trivial, [f[_,_]] =>> Exobifunctor[==>, f, >->, ⊙]] =
    new LaxSemigroupalK2.Proto[Either, * => *, (*,*), Trivial, [f[_,_]] =>> Exobifunctor[==>, f, >->, ⊙]]:
      def A: Associative.Aux[Function, Tuple2, Trivial] = summon
      def product[F[_,_], G[_,_]]: ((Exobifunctor[==>, F, >->, ⊙], Exobifunctor[==>, G, >->, ⊙])) => Exobifunctor[==>, [a, b] =>> Either[F[a, b], G[a, b]], >->, ⊙] =
        P => new Exobifunctor[==>, [a, b] =>> Either[F[a, b], G[a, b]], >->, ⊙]:
          def bimap[A, X, B, Y](l: A ==> X, r: Either[F[B, Y], G[B, Y]]): A ⊙ B >-> (X ⊙ Y) =
            r.fold(P._1.bimap(l, _), P._2.bimap(l, _))
  given laxArrow3[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]]: LaxSemigroupalK2.Aux[(*,*), * => *, (*,*), Trivial, [f[_,_]] =>> Exobifunctor[==>, -->, f, ⊙]] =
    new LaxSemigroupalK2.Proto[(*,*), * => *, (*,*), Trivial, [f[_,_]] =>> Exobifunctor[==>, -->, f, ⊙]]:
      def A: Associative.Aux[Function, Tuple2, Trivial] = summon
      def product[F[_,_], G[_,_]]: ((Exobifunctor[==>, -->, F, ⊙], Exobifunctor[==>, -->, G, ⊙])) => Exobifunctor[==>, -->, [a, b] =>> (F[a, b], G[a, b]), ⊙] =
        P => new Exobifunctor[==>, -->, [a, b] =>> (F[a, b], G[a, b]), ⊙]:
          def bimap[A, X, B, Y](l: A ==> X, r: B --> Y): (F[A ⊙ B, X ⊙ Y], G[A ⊙ B, X ⊙ Y]) =
            (P._1.bimap(l, r), P._2.bimap(l, r))

end ExobifunctorImplicits


object ExobifunctorHelpers:
  

end ExobifunctorHelpers
