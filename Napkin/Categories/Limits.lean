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
A cone over this diagram is an object $`A` and arrows over $`X` and $`Y` which make the diagram commute.
As per {cite}`ref:msci`, we call this cone a *fork*.
The name coming from the shape obtained if one writes $`A \to X \rightrightarrows Y` all in the same line; but to emphasize the cone-ness, we have bent the fork in our pictures.

Effectively, the arrow over $`Y` is just forcing $`f \circ q = g \circ q`.
In any case, the *equalizer* of $`f` and $`g` is a "universal fork": it is an object $`E` and a map $`E \xrightarrow{e} X` such that for each $`A \xrightarrow{q} X` (with $`f \circ q = g \circ q`), the map $`q` factors uniquely through $`E`; that is, there is a unique $`A \xrightarrow{h} E` with $`q = e \circ h`.

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

:::aside "Equalizers in Mathlib"
The universal fork is the pair {name}`CategoryTheory.Limits.Fork` (a cone over the two parallel arrows) and {name}`CategoryTheory.Limits.equalizer` (the chosen apex when it exists, guarded by the {name}`CategoryTheory.Limits.HasEqualizer` hypothesis).
The universal property is delivered by `equalizer.lift`: any map killing the difference of `f` and `g` factors through the equalizer.

```lean
open CategoryTheory CategoryTheory.Limits in
noncomputable example {C : Type*} [Category C] {X Y : C} (f g : X ⟶ Y)
    [HasEqualizer f g] : C :=
  equalizer f g
```
:::

# Pullback squares

The same universal-cone idea, applied to a diagram $`X \xrightarrow{f} Z \xleftarrow{g} Y` (a *cospan*), produces the *pullback*: the universal object $`P` with maps to $`X` and $`Y` agreeing after composing into $`Z`.
In $`\mathsf{Set}` it is $`\{(x, y) \mid f(x) = g(y)\}`, the fibered product.
A prototypical geometric example glues local data: the differentiable functions on $`(-3, 1)` and on $`(-1, 3)` that agree on the overlap $`(-1, 1)` assemble, via a pullback, into the differentiable functions on $`(-3, 3)`.

:::aside "Pullbacks in Mathlib"
Mathlib's {name}`CategoryTheory.Limits.pullback` is the apex of this cospan cone, available whenever {name}`CategoryTheory.Limits.HasPullback` holds; `pullback.fst` and `pullback.snd` are its two legs and `pullback.lift` its universal map.
:::

# Limits

We've defined cones over discrete sets of $`X_i` (to get products) and over pairs of arrows (to get forks).
It turns out you can also define a cone over any general *diagram* of objects and arrows; we specify a projection from $`A` to each object and require that the projections from $`A` commute with the arrows in the diagram.

If you then demand the cone be universal, you have the extremely general definition of a *limit*.
As always, these are unique up to unique isomorphism.
We can also define the dual notion of a *colimit* in the same way.

:::aside "Limits in Mathlib"
A diagram is a functor $`F \colon J \to C` out of an indexing category $`J`, a cone over it is {name}`CategoryTheory.Limits.Cone`, and a universal cone is witnessed by {name}`CategoryTheory.Limits.IsLimit`.
The chosen limit {name}`CategoryTheory.Limits.limit` exists under {name}`CategoryTheory.Limits.HasLimit`, and products, equalizers, and pullbacks are all the special cases where $`J` is discrete, a parallel pair, or a cospan.
:::

# Problems

:::PROBLEM "Equalizers are monic"
Show that the equalizer of any diagram $`X \rightrightarrows Y` is monic.
:::
