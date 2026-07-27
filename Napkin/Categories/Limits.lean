import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

open CategoryTheory CategoryTheory.Limits

set_option pp.rawOnError true

#doc (Manual) "Limits in categories" =>

%%%
file := "Limits-in-categories"
%%%

We saw near the start of our category theory chapter the nice construction of products by drawing a bunch of arrows.
It turns out that this concept can be generalized immensely, and I want to give you a taste of that here.

To run this chapter, we follow the approach of {cite}`ref:msci`.

# Equalizers

:::PROTOTYPE
The equalizer of $`f, g \colon X \to Y` is the set of points with $`f(x) = g(x)`.
:::

Given two sets $`X` and $`Y`, and maps $`X \xrightarrow{f, g} Y`, we define their *equalizer* to be $$`\left\{ x \in X \mid f(x) = g(x) \right\}.`
We would like a categorical way of defining this, too.

Consider two objects $`X` and $`Y` with two maps $`f` and $`g` between them.

:::figure "figures/category-theory/equalizer-parallel.svg"
The parallel pair $`f, g \colon X \to Y` we take the equalizer of.
:::

A cone over this diagram is an object $`A` and arrows over $`X` and $`Y` which make the diagram commute.
As per {cite}`ref:msci`, we call this cone a *fork*.
The name coming from the shape obtained if one writes $`A \to X \rightrightarrows Y` all in the same line; but to emphasize the cone-ness, we have bent the fork in our pictures.

Effectively, the arrow over $`Y` is just forcing $`f \circ q = g \circ q`.

:::figure "figures/category-theory/equalizer-fork.svg"
A fork: a map $`q` into $`X` with $`f \circ q = g \circ q`.
:::
In any case, the *equalizer* of $`f` and $`g` is a "universal fork": it is an object $`E` and a map $`E \xrightarrow{e} X` such that for each $`A \xrightarrow{q} X` (with $`f \circ q = g \circ q`), the map $`q` factors uniquely through $`E`; that is, there is a unique $`A \xrightarrow{h} E` with $`q = e \circ h`.

:::figure "figures/category-theory/equalizer-universal.svg"
The equalizer $`E` is the universal fork: every fork factors uniquely through it.
:::

Again, the dotted arrows can be omitted, and as before equalizers may not exist.
But when they do exist:

:::EXERCISE
If $`E \xrightarrow{e} X` and $`E' \xrightarrow{e'} X` are equalizers, show that $`E \cong E'`.
:::

:::EXAMPLE "Examples of equalizers"
1. In $`\mathsf{Set}`, given $`X \xrightarrow{f, g} Y` the equalizer $`E` can be realized as $`E = \{x \mid f(x) = g(x)\}`, with the inclusion $`e \colon E \hookrightarrow X` as the morphism.
   As usual, by abuse we'll often just refer to $`E` as the equalizer.
2. Ditto in $`\mathsf{Top}`, $`\mathsf{Grp}`.
   One has to check that the appropriate structures are preserved (e.g. one should check that $`\{\phi(g) = \psi(g) \mid g \in G\}` is a group).
3. In particular, given a homomorphism $`\phi \colon G \to H`, the inclusion $`\ker\phi \hookrightarrow G` is an equalizer for $`\phi \colon G \to H` and the trivial homomorphism $`G \to H`.
:::

According to (c) equalizers let us get at the concept of a kernel if there is a distinguished "trivial map", like the trivial homomorphism in $`\mathsf{Grp}`.
We'll flesh this idea out in the chapter on abelian categories.

# Pullback squares

The same universal-cone idea, applied to a diagram $`X \xrightarrow{f} Z \xleftarrow{g} Y` (a *cospan*), produces the *pullback*: the universal object $`P` with maps to $`X` and $`Y` agreeing after composing into $`Z`.
In $`\mathsf{Set}` it is $`\{(x, y) \mid f(x) = g(y)\}`, the fibered product.
A prototypical geometric example glues local data: the differentiable functions on $`(-3, 1)` and on $`(-1, 3)` that agree on the overlap $`(-1, 1)` assemble, via a pullback, into the differentiable functions on $`(-3, 3)`.

# Limits

We've defined cones over discrete sets of $`X_i` (to get products) and over pairs of arrows (to get forks).
It turns out you can also define a cone over any general *diagram* of objects and arrows; we specify a projection from $`A` to each object and require that the projections from $`A` commute with the arrows in the diagram.

If you then demand the cone be universal, you have the extremely general definition of a *limit*.
As always, these are unique up to unique isomorphism.
We can also define the dual notion of a *colimit* in the same way.

# Problems

:::PROBLEM "Equalizers are monic"
Show that the equalizer of any diagram $`X \rightrightarrows Y` is monic.
:::

# Formalization

:::LEANCOMPANION
:::

## Equalizers

The universal fork is the pair {name}`CategoryTheory.Limits.Fork` (a cone over the two parallel arrows) and {name}`CategoryTheory.Limits.equalizer` (the chosen apex when it exists, guarded by the {name}`CategoryTheory.Limits.HasEqualizer` hypothesis).
The universal property is delivered by `equalizer.lift`: any map killing the difference of `f` and `g` factors through the equalizer, and the leg `equalizer.ι` satisfies `f ∘ e = g ∘ e`.

```lean
noncomputable example {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)
    [HasEqualizer f g] : C :=
  equalizer f g

example {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)
    [HasEqualizer f g] : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
  equalizer.condition f g
```

The exercise asked you to show that two equalizers $`E \xrightarrow{e} X` and $`E' \xrightarrow{e'} X` of the same parallel pair are isomorphic.
Universality does all the work: two forks that are both universal have canonically isomorphic apexes, packaged as {name}`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`.

```lean
example {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)
    (c c' : Fork f g) (hc : IsLimit c) (hc' : IsLimit c') : c.pt ≅ c'.pt :=
  IsLimit.conePointUniqueUpToIso hc hc'
```

That one-liner hides the actual reason the isomorphism exists, so build it by hand and watch it fall out of the universal property.
Lift each apex through the other's universality (`hc'.lift c` and `hc.lift c`, using {name}`CategoryTheory.Limits.IsLimit.lift`) to get the two comparison maps.
Each round-trip is a map from a universal fork to itself, and a map into a limit is pinned down by its composites with the legs: {name}`CategoryTheory.Limits.IsLimit.hom_ext` reduces the two `id` goals leg-by-leg, where {name}`CategoryTheory.Limits.IsLimit.fac` (a `simp` lemma) recovers each leg from the lift that built it.

:::exercise
```lean
example {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)
    (c c' : Fork f g) (hc : IsLimit c) (hc' : IsLimit c') : c.pt ≅ c'.pt := by
  sorry
```
:::

:::solution
```lean
example {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)
    (c c' : Fork f g) (hc : IsLimit c) (hc' : IsLimit c') :
    c.pt ≅ c'.pt where
  -- The comparison maps: lift each apex through the other's universality.
  hom := hc'.lift c
  inv := hc.lift c'
  -- Each round-trip agrees with the identity on every leg, so `hom_ext`
  -- (with `fac` firing through `simp`) collapses it to `𝟙`.
  hom_inv_id := hc.hom_ext (by simp)
  inv_hom_id := hc'.hom_ext (by simp)
```
:::

A later problem asks you to show the equalizer map $`E \xrightarrow{e} X` is a monomorphism.
For the *chosen* equalizer Mathlib already records this as an instance.

```lean
example {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)
    [HasEqualizer f g] : Mono (equalizer.ι f g) :=
  inferInstance
```

But it holds for any universal fork, and the proof is a good illustration of what universality buys.
Prove it.
Unfold `Mono` with `constructor` and it asks exactly for cancellation: two maps $`u, v \colon W \to E` with $`u e = v e` are equal.
That is the uniqueness half of the universal property, `CategoryTheory.Limits.Fork.IsLimit.hom_ext`: a map *into* a universal fork is pinned down by its composite with the single leg, so agreeing there is agreeing.
Notice that nothing about equalizers as such is used — the same argument shows any limit leg is monic in the corresponding sense.

:::exercise
```lean
example {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y}
    (c : Fork f g) (hc : IsLimit c) : Mono (Fork.ι c) := by
  sorry
```
:::

:::solution
```lean
example {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y}
    (c : Fork f g) (hc : IsLimit c) : Mono (Fork.ι c) := by
  constructor
  intro W u v h
  -- Two maps into a universal fork agreeing on the leg are equal.
  exact Fork.IsLimit.hom_ext hc h
```
:::

## Pullback squares

Mathlib's {name}`CategoryTheory.Limits.pullback` is the apex of this cospan cone, available whenever {name}`CategoryTheory.Limits.HasPullback` holds; `pullback.fst` and `pullback.snd` are its two legs and `pullback.lift` its universal map.
The two legs agree after composing into the base, which is exactly `pullback.condition`.

```lean
noncomputable example {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : C :=
  pullback f g

example {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] : pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  pullback.condition
```

Those two facts *are* the pullback, in the following sense: any other commuting square over the same cospan factors through it, uniquely.
Prove the existence half, which is what earns $`X \times_Z Y` its name.
Given $`h \colon W \to X` and $`k \colon W \to Y` whose composites into $`Z` agree, `pullback.lift` produces the comparison map, and `pullback.lift_fst` and `pullback.lift_snd` say it really does restrict to $`h` and $`k` — so the proof is one anonymous constructor supplying a witness together with its two properties.

:::exercise
```lean
example {C : Type*} [Category C] {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    ∃ u : W ⟶ pullback f g,
      u ≫ pullback.fst f g = h ∧ u ≫ pullback.snd f g = k := by
  sorry
```
:::

:::solution
```lean
example {C : Type*} [Category C] {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    ∃ u : W ⟶ pullback f g,
      u ≫ pullback.fst f g = h ∧ u ≫ pullback.snd f g = k :=
  ⟨pullback.lift h k w, pullback.lift_fst h k w, pullback.lift_snd h k w⟩
```
:::

## Limits

A diagram is a functor $`F \colon J \to C` out of an indexing category $`J`, a cone over it is {name}`CategoryTheory.Limits.Cone`, and a universal cone is witnessed by {name}`CategoryTheory.Limits.IsLimit`.
The chosen limit {name}`CategoryTheory.Limits.limit` exists under {name}`CategoryTheory.Limits.HasLimit`, and products, equalizers, and pullbacks are all the special cases where $`J` is discrete, a parallel pair, or a cospan.

```lean
noncomputable example {J C : Type*} [Category J] [Category C] (F : J ⥤ C)
    [HasLimit F] : C :=
  limit F

example {J C : Type*} [Category J] [Category C] (F : J ⥤ C) (c : Cone F)
    (hc : IsLimit c) (c' : Cone F) : c'.pt ⟶ c.pt :=
  hc.lift c'
```

Every argument in this section — the equalizer of two forks being unique, the equalizer leg being monic, the pullback comparison map — used the same two moves, existence and uniqueness of a map into a universal cone, and both survive the generalisation.
Prove the uniqueness move in its general form: two maps into a limit that agree after every leg are equal.
The single ingredient is {name}`CategoryTheory.Limits.IsLimit.hom_ext`, and the legs of a cone `c` are `c.π.app j`, one for each object `j` of the indexing category.
Having this, re-read the equalizer proofs above: `Fork.IsLimit.hom_ext` is this lemma specialised to a two-object indexing category, where checking "every leg" collapses to checking one.

:::exercise
```lean
example {J C : Type*} [Category J] [Category C] (F : J ⥤ C) (c : Cone F)
    (hc : IsLimit c) {W : C} (u v : W ⟶ c.pt)
    (h : ∀ j, u ≫ c.π.app j = v ≫ c.π.app j) : u = v := by
  sorry
```
:::

:::solution
```lean
example {J C : Type*} [Category J] [Category C] (F : J ⥤ C) (c : Cone F)
    (hc : IsLimit c) {W : C} (u v : W ⟶ c.pt)
    (h : ∀ j, u ≫ c.π.app j = v ≫ c.π.app j) : u = v :=
  hc.hom_ext h
```
:::
