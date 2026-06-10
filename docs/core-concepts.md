# Core concepts

Everything in exo is built from a small set of primitives that live directly in the `io.github.cosmin33.exo` package. This page covers them in dependency order: universal quantifiers, natural transformations, isomorphisms, kind witnesses, and the product/sum encodings.

## The four kind levels

A naming convention runs through the entire library. Most abstractions exist at four "kind levels", distinguished by suffix:

| Suffix | Quantifies over | Example shape |
|---|---|---|
| *(none)* | plain types `A` | `Iso[->, A, B]` |
| `K` | type constructors `F[_]` | `IsoK[->, F, G]` |
| `K2` | binary constructors `F[_,_]` | `IsoK2[->, F, G]` |
| `H` | higher-order shapes `A[_[_]]` | `IsoH[->, A, B]` |

Once you understand an abstraction at the plain level, the `K`/`K2`/`H` variants are the same idea one kind up.

## Universal quantifiers: `∀`, `∀∀`, `∀∀∀`, `∀~`, `∀~~`, `∀≈`

Scala has no first-class universally quantified *types*, so exo Church-encodes them. `∀[F]` is a value that can be specialized to `F[A]` for every `A`:

```scala
type ∀[F[_]]        // "for all a, F[a]"        (Forall)
type ∀∀[F[_,_]]     // "for all a b, F[a,b]"    (Forall2)
type ∀∀∀[F[_,_,_]]  // arity 3                  (Forall3)
type ∀~[A[_[_]]]    // "for all f[_], A[f]"     (ForallK)
type ∀~~[A[_[_,_]]] // over binary constructors (ForallK2)
type ∀≈[A[_[_[_]]]] // over higher kinds        (ForallHK)
```

Construction goes through `of`/`mk`/`from` (or directly from a polymorphic function literal); elimination is `apply`/`specialize`:

```scala
val lengths: ∀[[a] =>> List[a] => Int] = ∀.mk[∀[[a] =>> List[a] => Int]](_.length)
lengths[String](List("x", "y"))  // 2
```

Internally `∀[F]` erases to `F[Any]` — the abstraction is sound because the only way to build one is with a genuinely parametric function. The `Forall` module also proves useful distribution laws, e.g. `∀[[x] =>> F[x] ⨂ G[x]] <=> (∀[F] ⨂ ∀[G])` and `∀[[a] =>> ∀[[b] =>> F[a,b]]] <=> ∀∀[F]`.

## Natural transformations: `~>`, `~~>`, `≈>`

Natural transformations are just universally quantified functions, so they are defined as aliases over the quantifiers:

```scala
type ~> [F[_], G[_]]       = ∀[[a] =>> F[a] => G[a]]
type ~~> [F[_,_], G[_,_]]  = ∀∀[[a, b] =>> F[a, b] => G[a, b]]
type ≈> [A[_[_]], B[_[_]]] = ∀~[[f[_]] =>> A[f] => B[f]]
```

Each has a companion with a convenient constructor taking a Scala 3 polymorphic function:

```scala
val head: List ~> Option  = ~>([A] => (l: List[A]) => l.headOption)
val toList: Option ~> List = ~>([A] => (o: Option[A]) => o.toList)

head.run(List(1, 2, 3))      // Some(1)
(head andThen toList)        // List ~> List, via syntax
```

Reversed arrows exist too (`<~`, `<~~`, `<≈`), as do invertible versions (next section).

## Isomorphisms: `Iso`, `<=>`, `<~>`, `<~~>`, `<≈>`

`Iso[->, A, B]` is an isomorphism *in an arbitrary category* `->`: a pair of arrows `to: A -> B` and `from: B -> A`, together with the `Semicategory` they compose in.

```scala
trait Iso[->[_,_], A, B]:
  def cat: Semicategory[->]
  def to:   A -> B
  def from: B -> A
```

Operations: `flip`, `andThen`/`compose`, `chain` (compose through implicit search), `derive[F]` (transport an `F[A]` to `F[B]` given an iso-functor), and combinators `and`/`or`//\`/`\/` that pair isos through products and sums. Constructors are `Iso.unsafe(to, from)` (you promise the laws) and `Iso.refl`.

The common aliases fix the category and kind level:

```scala
type <=>[A, B]          = Iso[Function, A, B]   // iso of types
type <~>[F[_], G[_]]    = IsoK[* => *, F, G]    // natural isomorphism
type <~~>[F[_,_], G[_,_]] = IsoK2[* => *, F, G]
type <≈>[A[_[_]], B[_[_]]] = IsoH[* => *, A, B]
```

where `IsoK[->, F, G] = ∀[[a] =>> Iso[->, F[a], G[a]]]` and similarly for `K2`/`H`.

### `HasIso`: isomorphisms by implicit search

`HasIso[->, A, B]` is an opaque wrapper around `Iso[->, A, B]` with a tiered implicit search: it is derived from a type equality `A === B`, from an explicit `Iso[->, A, B]` in scope, or from the flipped `Iso[->, B, A]`. This is what powers `iso.chain[C]` and the summoner `<=>[A, B]`. `HasIsoK`, `HasIsoK2`, and `HasIsoH` do the same at higher kinds.

## Kind witnesses: `TypeK`, `IsKind`, `HasTc`

Sometimes a type constructor needs to be passed where only a plain type fits (e.g. as an object of a category). exo reifies constructors as types:

- **`TypeK[F[_]]`** (and `TypeK2`, `TypeHK`) — a "name" for `F` at kind `*`. Injective: `TypeK[F] === TypeK[G]` implies `F =~= G`.
- **`IsKind[A]`** — evidence that the plain type `A` stands for some constructor, exposed as the type member `Type[_]`. `IsKind.Aux[TypeK[List], List]` holds, and instances compose through pairs and sums: `IsKind[(TypeK[Option], TypeK[List])]` resolves with `Type = [a] =>> (Option[a], List[a])`.
- **`HasTc[TC[_[_]], TF]`** — bundles an `IsKind` witness for `TF` with a type-class instance `TC[F]` for the constructor it names. `HasTc[Monad', TypeK[List]]` is the "plain type" form of `Monad'[List]`, with an isomorphism between the two encodings.

`IsKind2`/`HasTc2` and `IsHKind`/`HasHc` repeat the pattern for `F[_,_]` and `A[_[_]]`.

## Products and sums: `/\` and `\/`

`Conjunction` and `Disjunction` are opaque aliases for `Tuple2` and `Either` with symbolic names and a few extras:

```scala
type /\[A, B]  // Conjunction; >: (A, B)
type \/[A, B]  // Disjunction; >: Either[A, B]
```

Both come with proofs of equality to their underlying type (`Tuple2 =~~= /\`, `Either =~~= \/`), bifunctor instances, and folding/swapping helpers. They are the canonical tensor (`⨂`) and cotensor (`⨁`) used by the `Cartesian`/`Cocartesian` instances for `Function`.

Two other basic types round out the toolkit:

- **`Void`** — a genuinely uninhabited type (`<: Nothing`), with `absurd` elimination and proofs `Void =!= Any`, `¬[Void]`. The initial object of the `Function` category.
- **`Trivial[A]`** — the constraint that holds for every type (an opaque `Unit`). Categories whose `TC` member is `Trivial` place no restriction on their objects. `TrivialK`/`TrivialK2`/`TrivialH` lift it to higher kinds.

## Syntax

`import io.github.cosmin33.exo.syntax.*` adds the fluent layer:

```scala
// on any arrow in any semicategory
f >>> g ; f <<< g ; f.andThen(g) ; f.compose(g)
f.flipped      // in a Groupoid
f.dual         // wrap as Dual[->, B, A]
f.merge(g)     // A -> (D /\ B) in a Cartesian category
f.split(g)     // (A \/ D) -> B in a Cocartesian category

// on values
a.isoTo[B]     // apply an implicit HasIso[Function, A, B]
a.left[B] ; a.right[B]

// on F[A] with an exofunctor in scope
fa.emap(f)     // covariant map through any arrow type
fa.ecomap(f)   // contravariant map

// on natural transformations (∀[[a] =>> F[a] -> G[a]])
nat1 >>> nat2 ; nat1 <<< nat2
```
