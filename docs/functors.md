# Functors

`io.github.cosmin33.exo.functors` is the library's namesake. An **exofunctor** is a functor between two arbitrary categories, given by their arrow types:

```scala
trait Exofunctor[==>[_,_], -->[_,_], F[_]]:
  def map[A, B](f: A ==> B): F[A] --> F[B]

type Exo[==>[_,_], -->[_,_], F[_]] = Exofunctor[==>, -->, F]
```

`F` maps objects; `map` maps arrows of the source category `==>` to arrows of the target category `-->`. Everything you'd usually reach for a separate type class for is an instantiation:

| Familiar concept | As an exofunctor |
|---|---|
| `Functor[F]` (cats) | `Exo[* => *, * => *, F]` — alias `Endofunctor.CovF[F]` |
| `Contravariant[F]` | `Exo[Dual[* => *,*,*], * => *, F]` — alias `Exocon` |
| `Invariant[F]` | functor from `Dicat` / iso category, e.g. `Isofunctor[F] = Exo[<=>, <=>, F]` |
| congruence (`A === B` ⟹ `F[A] === F[B]`) | `Exo[===, ===, F]` — exists for *every* `F` |
| covariance evidence | `Exo[<~<, <~<, F]` |

The last rows are the point: because the arrow is a parameter, even type *equality* and *subtyping* are categories functors can act on. From the tests:

```scala
def f1[F[_]]: Exo[===, ===, F]    = summon   // Leibniz congruence, free for all F
def f2[F[_]]: Exo[===, <~<, F]    = summon
def f3[F[_]]: Exo[===, * => *, F] = summon
def f4[F[_]]: Exo[===, <=>, F]    = summon
```

Functors compose: `F.compose(G): Exofunctor[==>, >->, [a] =>> G[F[a]]]`. With `import exo.syntax.*`, any `fa: F[A]` gains `fa.emap(f)` / `fa.ecomap(f)` for an in-scope covariant/contravariant exofunctor.

## Exobifunctor

```scala
trait Exobifunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]]:
  def bimap[A, X, B, Y](left: A ==> X, right: B --> Y): (A ⊙ B) >-> (X ⊙ Y)
  def leftMap [A, B, Z](fn: A ==> Z)(using SubcatHasId[-->, B]): (A ⊙ B) >-> (Z ⊙ B)
  def rightMap[A, B, Z](fn: B --> Z)(using SubcatHasId[==>, A]): (A ⊙ B) >-> (A ⊙ Z)
  def leftFunctor [X]: Exo[==>, >->, ⊙[*, X]]
  def rightFunctor[X]: Exo[-->, >->, ⊙[X, *]]
```

A functor of two arguments, possibly from two *different* source categories into a third. The aliases recover the usual zoo:

```scala
type Endobifunctor[->[_,_], ⊙[_,_]]  = Exobifunctor[->, ->, ->, ⊙]            // e.g. Tuple2, Either
type Endoprofunctor[->[_,_], ⊙[_,_]] = Exobifunctor[Dual[->,*,*], ->, ->, ⊙]  // e.g. -> itself
type Exoprofunctor[==>[_,_], -->[_,_], >->[_,_], ⊙[_,_]] =
  Exobifunctor[Dual[==>,*,*], -->, >->, ⊙]
```

A profunctor is just a bifunctor whose left source is the dual category — `promap(l, r) = bimap(Dual(l), r)`. Instances include `Tuple2`, `Either`, `/\`, `\/`, the hom-bifunctor of any semicategory (`(A -> B)` is contravariant in `A`, covariant in `B`), and instances lifted through `Dual`, `Prodcat`, and `Kleisli`.

`Exobifunctor.fromFaFunctors` builds a bifunctor from a coherent family of left and right unary functors.

## LaxSemigroupal and LaxMonoidal

A lax monoidal functor preserves tensor structure "up to a one-way map":

```scala
trait LaxSemigroupal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]]:
  type TD[_]
  def D: Associative.Aux[-->, ⊙-, TD]            // tensor in the target
  def product[A, B]: (F[A] ⊙- F[B]) --> F[A ⊙= B]

  def map2[==>[_,_], A, B, C](fn: (A ⊙= B) ==> C)(using Exo[==>, -->, F])
    : (F[A] ⊙- F[B]) --> F[C]
  def preserveCSemigroup[==>[_,_], M](ma: CSemigroup[==>, ⊙=, M])(using Exo[==>, -->, F])
    : CSemigroup[-->, ⊙-, F[M]]

trait LaxMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] extends LaxSemigroupal[⊙=, -->, ⊙-, F]:
  type ID; type IC
  def D: Monoidal.Aux[-->, ⊙-, TD, ID]
  def id: ID --> F[IC]
  def preserveCMonoid[==>[_,_], M](ma: CMonoid.Aux[==>, ⊙=, M, IC])(using Exo[==>, -->, F])
    : CMonoid.Aux[-->, ⊙-, F[M], ID]
```

Note there are *two* tensors: `⊙=` in the source and `⊙-` in the target; `product` is the structure map combining two `F`-values. `map2` is the applicative-style combinator that falls out, and `preserveCSemigroup`/`preserveCMonoid` are the classic theorems "monoidal functors carry monoids to monoids" — e.g. a semigroup on `M` yields a semigroup on `F[M]`.

Variations come from substituting categories rather than writing new traits:

```scala
type OplaxSemigroupal [⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] = LaxSemigroupal[⊙=, Dual[-->,*,*], ⊙-, F]  // structure map reversed
type StrongSemigroupal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] = LaxSemigroupal[⊙=, Iso[-->,*,*],  ⊙-, F]  // structure map invertible
type OplaxMonoidal    [⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]] = LaxMonoidal[⊙=, Dual[-->,*,*], ⊙-, F]
```

Lax monoidal functors compose (`compose`), threading identity preservation through.

## FrobeniusMonoidal

```scala
trait FrobeniusMonoidal[⊙=[_,_], -->[_,_], ⊙-[_,_], F[_]]:
  def functor:   LaxMonoidal  [⊙=, -->, ⊙-, F]   // product:   (F[A] ⊙- F[B]) --> F[A ⊙= B]
  def opFunctor: OplaxMonoidal[⊙=, -->, ⊙-, F]   // opProduct: F[A ⊙= B] --> (F[A] ⊙- F[B])
```

A functor that is simultaneously lax and oplax monoidal — it can both combine and split tensor structure.

## Higher-kind variants

As everywhere in exo, `K`/`K2`/`H` versions lift each of these one kind level. The pattern, shown for `ExofunctorK`:

```scala
trait ExofunctorK[==>[_,_], -->[_,_], A[_[_]]]:
  def map[F[_], G[_]](f: ∀[[a] =>> F[a] ==> G[a]]): A[F] --> A[G]
```

Where `Exofunctor.map` takes an arrow, `ExofunctorK.map` takes a *natural transformation* — `A` is a construction parameterized by a type constructor (think `FunctorK`/higher-order functors). Useful aliases:

```scala
type EndofunctorK[->[_,_], A[_[_]]] = ExofunctorK[->, ->, A]
type ContravariantK[A[_[_]]] = ExofunctorK[Dual[* => *,*,*], * => *, A]  // comap: (G ~> F) => A[F] => A[G]
```

`ExobifunctorK/K2/H`, `LaxSemigroupalK/K2/H`, and `LaxMonoidalK/K2/H` follow the same scheme, replacing arrows with `∀`-, `∀∀`-, or `∀~`-quantified arrow families.
