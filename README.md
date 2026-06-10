# exo

[![Maven Central](https://img.shields.io/maven-central/v/io.github.cosmin33/exo-core_3)](https://central.sonatype.com/artifact/io.github.cosmin33/exo-core_3)

**Exofunctors and categories for Scala 3** — a category-theory library built around functors between *arbitrary* categories, not just the category of Scala types and functions.

Where libraries like cats fix the category to `Function1` (so `Functor[F]` always means `(A => B) => F[A] => F[B]`), exo abstracts over the arrow itself. A functor in exo maps arrows of *any* source category to arrows of *any* target category — type equalities, subtyping evidence, isomorphisms, Kleisli arrows, dual arrows, or plain functions. Covariance, contravariance, and invariance stop being separate type classes and become choices of source category.

```scala
libraryDependencies += "io.github.cosmin33" %% "exo-core" % "0.0.1"
```

Cross-built for Scala 3 on the JVM and Scala.js.

## A taste

```scala
import io.github.cosmin33.exo.*

// Natural transformations as first-class values (∀ is a real type here)
val head: List ~> Option = ~>([A] => (l: List[A]) => l.headOption)
head.run(List(1, 2, 3))   // Some(1)

// Isomorphisms compose, flip, and lift through functors
val iso: Int <=> Int = <=>[Int]
summon[Iso[* => *, Int, Int]]

// One Exofunctor type class, many "functors":
import io.github.cosmin33.exo.functors.*
import io.github.cosmin33.exo.evidence.*

def f1[F[_]]: Exo[===, ===, F]    = summon  // every F respects type equality
def f2[F[_]]: Exo[===, * => *, F] = summon  // ...which weakens to a function
def f3[F[_]]: Exo[===, <=>, F]    = summon  // ...or to an isomorphism
```

The same generality runs through the whole library: every abstraction (categories, functors, isomorphisms, universal quantifiers) comes in four "kind levels" — for plain types, for `F[_]` type constructors (`K` suffix), for `F[_,_]` bifunctor-shaped constructors (`K2`), and for higher-order `A[_[_]]` shapes (`H`).

## What's inside

| Package | Contents |
|---|---|
| `exo` (root) | Universal quantifiers `∀`/`∀∀`/`∀~`, natural transformations `~>`/`~~>`/`≈>`, isomorphisms `Iso`/`<=>`/`<~>`, kind witnesses `TypeK`/`IsKind`/`HasTc`, products and sums `/\`/`\/`, the Yoneda lemma |
| `exo.categories` | `Semicategory`, `Subcat`, `Associative`, `Monoidal`, `Braided`, `Symmetric`, `Cartesian`, `Ccc`, `Distributive`, `Groupoid`, `Dual`, `Initial`/`Terminal`, `CSemigroup`/`CMonoid`, `Exoadjunction`, plus derived categories (`Prodcat`, `Dicat`, `Kleisli`, `Opp`) |
| `exo.functors` | `Exofunctor`, `Exobifunctor`, `LaxSemigroupal`, `LaxMonoidal`, `FrobeniusMonoidal`, with aliases like `Endofunctor`, `Endobifunctor`, `Endoprofunctor` |
| `exo.evidence` | Leibniz equality `===`, kind equality `=~=`/`=~~=`/`=≈=`, Liskov subtyping `<~<`, strict subtyping `</<`, apartness `=!=`, incomparability `>~<`, injectivity, parametricity axioms |
| `exo.variance` | `IsCovariant`, `IsContravariant`, `IsInvariant`, `IsConstant`, `StrictlyCovariant`, `StrictlyContravariant` — variance as *evidence*, derivable and composable |
| `exo.inhabitance` | `¬` / `¬¬` (negation and double negation), `Proposition`, `WeakProposition`, `Contractible` — constructive-logic tools backing the evidence types |

## Documentation

- [Core concepts](docs/core-concepts.md) — `∀` and friends, natural transformations, `Iso`, kind witnesses, products/sums, syntax
- [Categories](docs/categories.md) — the category type-class hierarchy, from `Semicategory` to cartesian closed
- [Functors](docs/functors.md) — `Exofunctor`, bifunctors, lax monoidal functors
- [Evidence, variance, and inhabitance](docs/evidence.md) — type equality, subtyping, variance proofs, propositions
- [Yoneda](docs/yoneda.md) — the Yoneda lemma and its corollaries, stated over any category

## Building

```
sbt +test          # run tests (zio-test) on JVM and JS
sbt +publishLocal  # publish locally
```

## Acknowledgements

The evidence machinery (`Is`, `As`, parametricity axioms) descends from Alexander Konovalov's [leibniz](https://github.com/alexknvl/leibniz) library, generalized here to higher kinds and integrated with the categorical core.

## License

[MIT](LICENSE)
