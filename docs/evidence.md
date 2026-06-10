# Evidence, variance, and inhabitance

These three packages form the proof layer of exo: type-level relations represented as values you can combine, transport, and (where the relation actually holds) summon. The design descends from [alexknvl/leibniz](https://github.com/alexknvl/leibniz), generalized to higher kinds.

The relations, at a glance:

| Type | Notation | Reads as |
|---|---|---|
| `Is[A, B]` | `A === B` | A and B are the same type (Leibniz) |
| `IsK[F, G]` | `F =~= G` | same type constructor |
| `IsK2[F, G]` | `F =~~= G` | same binary constructor |
| `IsHK[F, G]` | `F =≈= G` | same higher-order constructor |
| `As[A, B]` | `A <~< B` | A is a subtype of B (Liskov) |
| `StrictAs[A, B]` | `A </< B` | proper subtype (`<~<` and `=!=`) |
| `WeakApart[A, B]` | `A =!= B` | A and B are different types |
| `Incomparable[A, B]` | `A >~< B` | neither subtypes the other |

## Equality: `Is` and its higher kinds

```scala
sealed abstract class Is[A, B]:
  def subst[F[_]](fa: F[A]): F[B]   // Leibniz: substitute in any context
  def coerce(a: A): B
  def flip: B === A
  def andThen[C](bc: B === C): A === C
  def lift[F[_]]: F[A] === F[B]
```

`subst` is the whole definition — everything else derives from "equals may be substituted in any context". `Is.refl` is the only constructor; `Is.fromPredef` converts from Scala's `=:=`.

`IsK` (`=~=`), `IsK2` (`=~~=`), and `IsHK` (`=≈=`) state the same thing for `F[_]`, `F[_,_]`, and `F[_[_]]`. They substitute in higher-order contexts (`subst[Alg[_[_]]]`), lower to plain equalities (`isK.is[A]: F[A] === G[A]`, `isK.lower[T]: T[F] === T[G]`), and convert to natural isomorphisms (`isK2.toIso: F <~~> G`). These proofs are what let `Dual`, `/\`, and `\/` inherit entire instance hierarchies from `Opp`, `Tuple2`, and `Either` at zero cost.

## Subtyping: `As`, `As1`, `StrictAs`

```scala
sealed abstract class As[-A, +B]:
  def substCv[F[+_]](fa: F[A]): F[B]
  def substCt[F[-_]](fb: F[B]): F[A]
  def apply(a: A): B
  def liftCo[F[+_]]: F[A] <~< F[B]
  def liftCt[F[-_]]: F[B] <~< F[A]
```

`A <~< B` is Liskov substitutability: it substitutes through covariant and contravariant contexts (per their declared variance), unlike `===` which substitutes through anything. `As.bracket(f: A <~< B, g: B <~< A): A === B` is antisymmetry.

- **`As1[A, B]`** is the bounds-explicit refinement: it exhibits types `A === Lower <: Upper === B`, which makes some proofs possible that the variance-annotated `As` cannot express directly.
- **`StrictAs[A, B]`** (`A </< B`) is a *proper* subtype: conformity `A <~< B` plus apartness `A =!= B`. Irreflexive — `StrictAs.irreflexive[A]` derives `Void` from `A </< A`.

## Apartness and incomparability

- **`WeakApart[A, B]`** (`A =!= B`) wraps a refutation `(A === B) => Void`. Notable: `decompose` gives the trichotomy `¬¬[(B </< A) \/ (A </< B) \/ (A >~< B)]` — two distinct types are strictly ordered one way, the other way, or incomparable. And `constant`: if `A =!= B` yet `F[A] === F[B]`, then `F` ignores its argument (`IsConstant[F]`).
- **`Incomparable[A, B]`** (`A >~< B`) is the proof that neither `A <~< B` nor `B <~< A` holds — e.g. `Int >~< String`.

## Injectivity and parametricity

- **`IsInjective[F]`**: from `F[A] === F[B]` conclude `A === B`. Composes, decomposes through composition, and is incompatible with `IsConstant[F]`. **`IsInjective2[F[_,_]]`** does both arguments at once, with given instances for `Tuple2`, `Either`, `/\`, `\/`, and `Function` — these power the `pairInjectivity` machinery in `IsKind`.
- **`Parametric[F]`** packages the free theorems: knowing how `F` behaves on *one* pair of types (e.g. `F[A] <~< F[B]` for some `A </< B`) determines its behavior on *all* pairs. Provided for every `F` as an axiom.
- **`Axioms`** is where the trusted base lives: `bracket` (antisymmetry), the four parametricity axioms, and extensionality, implemented with the unsafe coercions in `internal/Unsafe.scala`. Everything outside `Axioms`/`Unsafe` is honest derivation.

## Variance as evidence

`io.github.cosmin33.exo.variance` turns variance — normally a syntactic annotation — into a first-class, *semantic* property of any `F[_]`, annotated or not:

```scala
trait IsCovariant[F[_]]:
  def apply[A, B](using A <~< B): F[A] <~< F[B]

trait IsContravariant[F[_]]:
  def apply[A, B](using A <~< B): F[B] <~< F[A]

trait IsInvariant[F[_]]:                          // distinct args → incomparable results
  def apply[A, B](using A =!= B): F[A] >~< F[B]

trait IsConstant[F[_]]:                           // ignores its argument
  def apply[A, B]: F[A] === F[B]
```

Key facts:

- **Reification**: a syntactically covariant `F[+_]` automatically yields `IsCovariant[F]` (given `reify`); same for contravariance.
- **Single-witness sufficiency**: by parametricity, one strict example is enough — `witness1[F, A, B](using A </< B, F[A] <~< F[B]): IsCovariant[F]`.
- **Composition algebra**: covariant ∘ covariant = covariant, covariant ∘ contravariant = contravariant, etc., via `composeCo`/`composeCt`.
- **`StrictlyCovariant[F]` / `StrictlyContravariant[F]`** = injective + (co/contra)variant; they lift *strict* subtyping: `A </< B` gives `F[A] </< F[B]`.

## Inhabitance and propositions

`io.github.cosmin33.exo.inhabitance` supplies the constructive-logic substrate:

```scala
opaque type Uninhabited[A] <: A => Void          // ¬[A]   — A is impossible
opaque type Inhabited[A]   <: (A => Void) => Void // ¬¬[A] — A cannot be refuted
```

`¬¬` is a monad (`map`/`flatMap`), and classical principles hold under it: `Inhabited.lem[A]: ¬¬[¬[A] \/ A]`.

- **`Proposition[A]`** — proof-irrelevant types: any two values are equal, and a classical proof can be realized (`proved(using ¬¬[A]): A`). All evidence types in this library (`===`, `<~<`, `=!=`, `IsCovariant`, ...) are propositions, which is what makes them safe to treat as mere evidence.
- **`WeakProposition[A]`** — the weaker form: all inhabited subtypes of `A` are equal.
- **`Contractible[A]`** — inhabited + weakly propositional: a type with exactly one value up to equality, with `contract: B === A` for any inhabited `B <~< A`.

## The `internal` package

Implementation backing, mostly not user-facing:

- `Unsafe.scala` — the coercions implementing `Axioms` (the trust boundary).
- `Function1Instances.scala` — the category-theory instances for ordinary functions: `Distributive`/`Cartesian`/`Cocartesian`/`Ccc` over `Tuple2`/`Either` (and `/\`/`\/`), `Initial` (`Void`), `Terminal` (`Unit`).
- `LiskovInstances.scala` — `<~<` as a category (with `&` and `|` as its tensors), `EvidenceCatInstances.scala` — categories of evidence-carrying arrows.
- `DualInstances.scala`, `ProdcatInstances.scala` — instances transported to `Dual` and `Prodcat` via the Leibniz proofs.
- `FunctionKFunctions.scala` (+ `K2`, `HK`) — combinators backing the `~>`/`~~>`/`≈>` companions.
- `any.scala` — the `|>` pipe operator and small helpers.
