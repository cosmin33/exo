# Categories

`io.github.cosmin33.exo.categories` defines categories as type classes over an arrow type `->[_,_]`. A category here is *not* tied to Scala functions: `Function1`, Leibniz equality `===`, Liskov subtyping `<~<`, isomorphisms `Iso[->,*,*]`, Kleisli arrows, and dual arrows all form categories, and every abstraction on this page works uniformly over them.

Every trait on this page also exists at higher kind levels with the `K`/`K2`/`H` suffixes (e.g. `SemicategoryK` composes natural transformations `∀[[a] =>> F[a] -> G[a]]`); each higher variant has a `.lower` back to the plain level. See [core concepts](core-concepts.md#the-four-kind-levels).

## The hierarchy

```
Semicategory                    composition only
  └─ Subcategory (Subcat)      + identities for objects with TC
       ├─ Groupoid             + every arrow invertible
       ├─ Concrete             + forgetful map to functions
       └─ Distributive         + cartesian and cocartesian structure that distribute

Associative[->, ⊙]              tensor with associator
  └─ Monoidal                  + unit object Id with unitors
  └─ Braided                   + braid: A⊙B -> B⊙A
       └─ Symmetric            + braid is self-inverse
            └─ Cartesian       + projections fst/snd and diagonal  (Monoidal too)
                 └─ Ccc        + exponentials with curry/uncurry
```

## Semicategory and Subcat

```scala
trait Semicategory[->[_,_]]:
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C

trait Subcategory[->[_,_]] extends Semicategory[->]:
  type TC[_]
  def id[A: TC]: A -> A

type Subcat[->[_,_]] = Subcategory[->]
```

A `Semicategory` is a category without identities. `Subcat` adds them — but only for objects satisfying the constraint `TC[_]`. This type member is the library's way of modeling **subcategories of Set**: the full category of Scala types uses `TC = Trivial` (every type qualifies; alias `Subcat.AuxT[->]`), while a restricted category can demand e.g. an ordering or a proposition on its objects. `Subcat.Aux[->, TC0]` pins the member.

`SubcatHasId[->, A]` is the convenience capability "this category has an identity at `A`", used pervasively as a context bound.

## Tensor structure: Associative → Monoidal

```scala
trait Associative[->[_,_], ⊙[_,_]]:
  type TC[_]
  def C: Subcat.Aux[->, TC]
  def bifunctor: Endobifunctor[->, ⊙]
  def associate  [X: TC, Y: TC, Z: TC]: ((X ⊙ Y) ⊙ Z) -> (X ⊙ (Y ⊙ Z))
  def diassociate[X: TC, Y: TC, Z: TC]: (X ⊙ (Y ⊙ Z)) -> ((X ⊙ Y) ⊙ Z)
  // derived: grouped(f, g), strongFirst, strongSecond, isoAssociator, ...

trait Monoidal[->[_,_], ⊙[_,_]] extends Associative[->, ⊙]:
  type Id
  def idl[A: TC]: (Id ⊙ A) -> A   ;  def coidl[A: TC]: A -> (Id ⊙ A)
  def idr[A: TC]: (A ⊙ Id) -> A   ;  def coidr[A: TC]: A -> (A ⊙ Id)
```

`Associative` equips a category with a tensor `⊙` (a bifunctor with an associator iso); `Monoidal` adds the unit object `Id` and the unitor isos. For `Function` with `Tuple2` the unit is `Unit`; with `Either` (via duality) it's `Void`.

## Braided, Symmetric, Cartesian, Cocartesian

```scala
trait Braided[->[_,_], ⊙[_,_]] extends Associative[->, ⊙]:
  def braid[A: TC, B: TC]: (A ⊙ B) -> (B ⊙ A)

trait Symmetric[->[_,_], ⊙[_,_]] extends Braided[->, ⊙]   // braid ∘ braid = id

trait Cartesian[->[_,_], ⨂[_,_]] extends Monoidal[->, ⨂] with Symmetric[->, ⨂]:
  def fst[A: TC, B: TC]: (A ⨂ B) -> A
  def snd[A: TC, B: TC]: (A ⨂ B) -> B
  def diag[A: TC]: A -> (A ⨂ A)
  def &&&[X, Y, Z](f: X -> Y, g: X -> Z): X -> (Y ⨂ Z)
```

**Cocartesian structure is cartesian structure in the dual category** — there is no separate trait:

```scala
type Cocartesian[->[_,_], ⨂[_,_]] = Cartesian[Dual[->,*,*], ⨂]
// extension methods recover the familiar vocabulary:
//   inl, inr, |||, codiag, ...
```

For `Function`: `Cartesian[* => *, Tuple2]` (and `/\`) and `Cocartesian[* => *, Either]` (and `\/`) are provided.

## Ccc — cartesian closed categories

```scala
trait Ccc[->[_,_], ⊙[_,_], |->[_,_]] extends Cartesian[->, ⊙]:
  def curry  [A, B, C](f: (A ⊙ B) -> C): A -> (B |-> C)
  def uncurry[A, B, C](f: A -> (B |-> C)): (A ⊙ B) -> C
  def apply[A, B](using TC[A |-> B]): ((A |-> B) ⊙ A) -> B
```

`|->` is the internal hom (exponential object). For `Function` the exponential is `Function` itself, and `curry`/`uncurry` are ordinary currying. `isoClosedAdjunction` states the defining adjunction `(A ⊙ X) -> B  <=>  A -> (X |-> B)`, and `closedAdjunction` packages it as an `Exoadjunction`.

## Distributive

```scala
trait Distributive[->[_,_], ⨂[_,_], ⨁[_,_]] extends Subcat[->]:
  def cartesian:   Cartesian.Aux[->, ⨂, TC, ProductId]
  def cocartesian: Cocartesian.Aux[->, ⨁, TC, SumId]
  def distribute[A: TC, B: TC, C: TC]: (A ⨂ (B ⨁ C)) -> ((A ⨂ B) ⨁ (A ⨂ C))
```

A category with products and sums where products distribute over sums. `Function` with `Tuple2`/`Either` (or `/\`/`\/`) is the canonical instance:

```scala
summon[Distributive[* => *, Tuple2, Either]]
```

## Other structures

- **`Groupoid[->]`** — a `Subcat` where every arrow flips: `def flip[A, B](f: A -> B): B -> A`. The category of isomorphisms `Iso[->,*,*]` is the canonical groupoid.
- **`Concrete[->]`** — a `Subcat` with a faithful mapping to functions: `concretize` turns an abstract arrow into a value-level function.
- **`Initial[->]` / `Terminal[->]`** — initial and terminal objects. `Terminal` is literally `Initial[Dual[->,*,*]]`. For `Function`: initial = `Void`, terminal = `Unit`, with the iso `(Init -> A) <=> Unit` as the uniqueness statement.
- **`CSemigroup[->, ⊙, A]` / `CMonoid[->, ⊙, A]`** — a semigroup/monoid *object*: `op: (A ⊙ A) -> A` (plus `id: I -> A` for monoids), stated in any associative/monoidal category rather than hard-coded to types-and-functions. Lax monoidal functors transport these across categories (see [functors](functors.md)).
- **`Exoadjunction[==>, -->, F, G]`** — an adjunction `F ⊣ G` between functors over two different arrow types, presented by the hom-iso `(F[A] ==> B) <=> (A --> G[B])`, with `unit`, `counit`, and monad/comonad-flavored `flatmap`/`coflatmap`.

## Derived categories

`categories/package.scala` builds new categories from old:

```scala
type Opp[->[_,_]]                  = [a, b] =>> b -> a       // reversed arrows, structurally
opaque type Dual[->[_,_], A, B]   <: B -> A                  // reversed arrows, nominally
type Prodcat[==>[_,_], -->[_,_], A, B] = (A ==> B, A --> B)  // product category
type Dicat[->[_,_], A, B]          = (A -> B, Dual[->, A, B]) // arrows both ways ≅ Iso
type Kleisli[->[_,_], F[_], A, B]  = A -> F[B]               // Kleisli category
```

- **`Dual`** is the workhorse: it carries Leibniz proofs (`Dual.leibniz`, and `Dual[Dual[->,*,*],*,*] =~~= ->` — the double dual cancels), so every structure on `->` transports to `Dual[->,*,*]` for free. This is how cocartesian, oplax, contravariant, and terminal-from-initial are all defined without duplicate traits.
- **`Dicat`** is isomorphic to `Iso[->,*,*]` (`Dicat.unsafeIsoIso`), and is the natural home of invariant functors.
- **`Kleisli[->, F, *, *]`** gets an `Endobifunctor` and a full `Cartesian` instance when `F` is lax semigroupal over the tensor — products of effectful arrows.
- **`Prodcat`** composes pointwise; `Prodcat.traverseDualEq` proves the product of duals is the dual of the product.
