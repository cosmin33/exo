# Yoneda

`io.github.cosmin33.exo.yoneda` states the Yoneda lemma — and its standard corollaries — as isomorphisms, parameterized over an arbitrary category `->` rather than hard-coded to functions. Because exo has first-class natural transformations (`~>`) and isomorphisms of types (`<=>`), the lemma is a value you can apply in both directions.

## The lemma

For a category `->`, an object `A` with an identity, and a `->`-functor `F`:

```scala
def lemmaYoIso[->[_,_], A, F[_]](using
  C: SubcatHasId[->, A],
  E: Exo.Cov[->, F]
): (->[A,*] ~> F) <=> F[A]
```

Natural transformations out of the hom-functor `A -> *` into `F` are in bijection with the values `F[A]`. The contravariant version (`lemmaCoyoIso`) does the same for `* -> A`.

## Embeddings and corollaries

```scala
// The Yoneda embedding is fully faithful:
def yoEmbedding  [->[_,_], A, B](using SubcatHasId[->, A]): (->[A,*] ~> ->[B,*]) <=> (B -> A)
def coyoEmbedding[->[_,_], A, B](using SubcatHasId[->, A]): (->[*,A] ~> ->[*,B]) <=> (A -> B)

// Naturally isomorphic hom-functors come from isomorphic objects:
def yoCorollary  [->[_,_], A, B](using ...): (->[A,*] <~> ->[B,*]) <=> Iso[->, B, A]
def coyoCorollary[->[_,_], A, B](using ...): (->[*,A] <~> ->[*,B]) <=> Iso[->, A, B]

// An arrow is the same as its action under every endofunctor:
def yoDoubleEmbed[->[_,_], A, B](using Subcat[->])
  : (A -> B) <=> ∀~[[f[_]] =>> Endofunctor[->, f] => f[A] -> f[B]]
```

## Specializations

`yoneda.function1` instantiates everything at `->` = `Function`, giving the formulations familiar from Haskell:

```scala
def lemmaYoIso[A, F[_]: Exo.CovF]: ((A => *) ~> F) <=> F[A]
def yoEmbedding[A, B]:  ((A => *) ~> (B => *)) <=> (B => A)
def yoCorol1[A, B]:     ((A => *) <~> (B => *)) <=> (B <=> A)
```

`yoneda.yonedaK` lifts the lemma one kind level: hom-functors of natural transformations versus higher-order functors `A[_[_]]`, with `≈>` in place of `~>`.

These isomorphisms are not just documentation — the implicit instances in `Iso`'s companion use them to derive isomorphisms between types automatically (e.g. recognizing `(A => *) ~> (B => *)` as `B => A` during `HasIso` search).
