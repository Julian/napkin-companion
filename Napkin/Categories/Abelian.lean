import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.FreydMitchell

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

open CategoryTheory
open CategoryTheory.Limits

set_option pp.rawOnError true

#doc (Manual) "Abelian categories" =>

%%%
file := "Abelian-categories"
%%%

In this chapter I'll translate some more familiar concepts into categorical language; this will require some additional assumptions about our category, culminating in the definition of a so-called "abelian category".
Once that's done, I'll be able to tell you what this "diagram chasing" thing is all about.

Throughout this chapter, "$`\hookrightarrow`" will be used for monic maps and "$`\twoheadrightarrow`" for epic maps.

# Zero objects, kernels, cokernels, and images

:::PROTOTYPE
In $`\mathsf{Grp}`, the trivial group and homomorphism are the zero objects and morphisms.
If $`G`, $`H` are abelian then the cokernel of $`\phi \colon G \to H` is $`H/\mathrm{img}\,\phi`.
:::

A *zero object* of a category is an object $`0` which is both initial and terminal; of course, it's unique up to unique isomorphism.
For example, in $`\mathsf{Grp}` the zero object is the trivial group, in $`\mathsf{Vect}_k` it's the zero-dimensional vector space consisting of one point, and so on.

:::QUESTION
Show that $`\mathsf{Set}` and $`\mathsf{Top}` don't have zero objects.
:::

For the rest of this chapter, all categories will have zero objects.

In a category $`\mathcal{A}` with zero objects, any two objects $`A` and $`B` thus have a distinguished morphism $$`A \to 0 \to B`
which is called the *zero morphism* and also denoted $`0`.
For example, in $`\mathsf{Grp}` this is the trivial homomorphism.

We can now define:

:::DEFINITION
Consider a map $`A \xrightarrow{f} B`.
The *kernel* is defined as the equalizer of this map and the map $`A \xrightarrow{0} B`.
Thus, it's a map $`\ker f \colon \mathrm{Ker}\, f \hookrightarrow A` such that $`f \circ \ker f = 0`, and moreover any other map with the same property factors uniquely through $`\mathrm{Ker}\, f` (so it is universal with this property).
Since the equalizer of any diagram is monic, $`\ker f` is a monic morphism, which justifies the use of "$`\hookrightarrow`".
:::

:::figure "figures/category-theory/kernel-univ.svg"
The kernel: $`\ker f` is universal among maps into $`A` whose composite with $`f` is $`0`.
:::

Notice that we're using $`\ker f` to represent the map and $`\mathrm{Ker}\, f` to represent the object.
Similarly, we define the cokernel, the dual notion:

:::DEFINITION
Consider a map $`A \xrightarrow{f} B`.
The *cokernel* of $`f` is a map $`\mathrm{coker}\, f \colon B \twoheadrightarrow \mathrm{Coker}\, f` such that $`\mathrm{coker}\, f \circ f = 0`, and moreover any other map with the same property factors uniquely through $`\mathrm{Coker}\, f` (so it is universal with this property).
Thus it is the "coequalizer" of this map and the map $`A \xrightarrow{0} B`.
Dually, $`\mathrm{coker}\, f` is an epic morphism, which justifies the use of "$`\twoheadrightarrow`".
:::

:::figure "figures/category-theory/cokernel-univ.svg"
The cokernel, dual to the kernel: $`\mathrm{coker}\, f` is universal among maps out of $`B` killing $`f`.
:::

Think of the cokernel of a map $`A \xrightarrow{f} B` as "$`B` modulo the image of $`f`".

:::EXAMPLE "Cokernels"
Consider the map $`\mathbb{Z}/6 \to D_{12} = \left\langle r, s \mid r^6 = s^2 = 1, rs = sr^{-1}\right\rangle`.
Then the cokernel of this map in $`\mathsf{Grp}` is $`D_{12} / \left\langle r \right\rangle \cong \mathbb{Z}/2`.
:::

This doesn't always work out quite the way we want since in general the image of a homomorphism need not be normal in the codomain.
Nonetheless, we can use this to define:

:::DEFINITION
The *image* of $`A \xrightarrow{f} B` is the kernel of $`\mathrm{coker}\, f`.
We denote $`\mathrm{Img}\, f = \mathrm{Ker}(\mathrm{coker}\, f)`.
This gives a unique map $`\mathrm{img}\, f \colon A \to \mathrm{Img}\, f`.
:::

When it exists, this coincides with our concrete notion of "image".
By universality of $`\mathrm{Img}\, f`, we find that there is a unique map $`\mathrm{img}\, f \colon A \to \mathrm{Img}\, f` that makes the entire diagram commute.

:::figure "figures/category-theory/image-factor.svg"
The image $`\mathrm{Img}\, f = \mathrm{Ker}(\mathrm{coker}\, f)`, through which $`f` factors.
:::

:::figure "figures/category-theory/kernel-image-cokernel.svg"
The kernel, image, and cokernel of a single map $`f \colon A \to B`.
:::

# Additive and abelian categories

:::PROTOTYPE
$`\mathsf{Ab}`, $`\mathsf{Vect}_k`, or more generally $`\mathsf{Mod}_R`.
:::

We can now define the notion of an additive and abelian category, which are the types of categories where this notion is most useful.

:::DEFINITION
An *additive category* $`\mathcal{A}` is one such that:

- $`\mathcal{A}` has a zero object, and any two objects have a product.
- More importantly: every $`\mathrm{Hom}_\mathcal{A}(A, B)` forms an _abelian group_ (written additively) such that composition distributes over addition: $$`(g + h) \circ f = g \circ f + h \circ f \quad\text{and}\quad f \circ (g + h) = f \circ g + f \circ h.`
  The zero map serves as the identity element for each group.
:::

In short:

:::MORAL
In an additive category, you can add two morphisms.
:::

Which is the only definition that makes sense anyway, we cannot talk about elements.

:::DEFINITION
An *abelian category* $`\mathcal{A}` is one with the additional properties that for any morphism $`A \xrightarrow{f} B`,

- The kernel and cokernel exist, and
- The morphism factors through the image so that $`\mathrm{img}(f)` is epic.
:::

:::EXAMPLE "Examples of abelian categories"
1. $`\mathsf{Vect}_k`, $`\mathsf{Ab}` are abelian categories, where $`f + g` takes its usual meaning.
2. Generalizing this, the category $`\mathsf{Mod}_R` of $`R`-modules is abelian.
3. $`\mathsf{Grp}` is not even additive, because there is no way to assign a commutative addition to pairs of morphisms.
:::

From now on, you can basically forget about additive category, we will be working in abelian category.

In general, once you assume a category is abelian, all the properties you would want of these kernels, cokernels, … that you would guess hold true.
For example,

:::PROPOSITION "Monic ⟺ trivial kernel"
A map $`A \xrightarrow{f} B` is monic if and only if its kernel is $`0 \to A`.
Dually, $`A \xrightarrow{f} B` is epic if and only if its cokernel is $`B \to 0`.
:::

::::PROOF
The easy direction is:

:::EXERCISE
Show that if $`A \xrightarrow{f} B` is monic, then $`0 \to A` is a kernel.
(This holds even in non-abelian categories.)
:::

Of course, since kernels are unique up to isomorphism, monic implies $`0` kernel.
On the other hand, assume that $`0 \to A` is a kernel of $`A \xrightarrow{f} B`.
For this we can exploit the group structure of the underlying homomorphisms now.
Assume $`Z \xrightarrow{g, h} A` with $`f \circ g = f \circ h`.

:::figure "figures/category-theory/preadditive-parallel.svg"
A parallel pair $`g, h \colon Z \to A` with $`f \circ g = f \circ h`.
:::
Then $`(g - h) \circ f = g \circ f - h \circ f = 0`, so $`g - h` factors through the kernel $`0 \to A`, giving $`g - h = 0`, i.e. $`g = h`.

:::figure "figures/category-theory/preadditive-diff.svg"
Replacing the parallel pair by the single map $`g - h`, which factors through the kernel.
:::
This is to say that $`f` is monic.
::::

:::PROPOSITION "Isomorphism ⟺ monic and epic"
In an abelian category, a map is an isomorphism if and only if it is monic and epic.
:::

:::PROOF
Omitted.
(The Freyd–Mitchell embedding theorem presented later implies this anyways for most situations we care about, by looking at a small sub-category.)
:::

# Exact sequences

:::PROTOTYPE
$`0 \to G \to G \times H \to H \to 0` is exact.
:::

Exact sequences will seem exceedingly unmotivated until you learn about homology groups, which is one of the most natural places that exact sequences appear.
In light of this, it might be worth trying to read the chapter on homology groups simultaneously with this one.

First, let me state the definition for groups, to motivate the general categorical definition.
A sequence of groups $$`G_0 \xrightarrow{f_1} G_1 \xrightarrow{f_2} G_2 \xrightarrow{f_3} \dots \xrightarrow{f_n} G_n`
is _exact_ at $`G_k` if the image of $`f_k` is the kernel of $`f_{k+1}`.
We say the entire sequence is exact if it's exact at $`k = 1, \dots, n - 1`.

:::EXAMPLE "Exact sequences"
1. The sequence $$`0 \to \mathbb{Z}/3 \xhookrightarrow{\times 5} \mathbb{Z}/15 \twoheadrightarrow \mathbb{Z}/5 \to 0`
   is exact.
   Actually, $`0 \to G \hookrightarrow G \times H \twoheadrightarrow H \to 0` is exact in general.
   (Here $`0` denotes the trivial group.)
2. For groups, the map $`0 \to A \to B` is exact if and only if $`A \to B` is injective.
3. For groups, the map $`A \to B \to 0` is exact if and only if $`A \to B` is surjective.
:::

If you look at the prototypical example, actually, a *short exact sequence* (an exact sequence of the form $`0 \to A \to B \to C \to 0`) is the most natural thing ever:

:::MORAL
It's basically just an equation $`C = B/A`.
:::

Whenever you see "there is a short exact sequence $`0 \to A \to B \to C \to 0`", you can mentally translate it to "$`C \cong B/A`"; but there's a slight difference: a group has more structure than a number, so the sequence also contains the information of the maps — the map that identifies $`A` with a subgroup of $`B`, and the map that identifies $`C` with the quotient group $`B/A`.

:::EXAMPLE "More exact sequences"
1. The sequence $`0 \to \mathbb{Z} \xrightarrow{\times 3} \mathbb{Z} \to \mathbb{Z}/3 \to 0` is short exact.
2. So is $`0 \to \mathbb{Z} \xrightarrow{\times 5} \mathbb{Z} \to \mathbb{Z}/5 \to 0`.

As you can see, the written equation "$`C \cong B/A`" is not completely accurate, the map $`A \to B` also matters in determining what $`C` is.
This also explains the common notation: the image of the map $`\mathbb{Z} \xrightarrow{\times 3} \mathbb{Z}` is usually written $`3\mathbb{Z}`, thus $`\mathbb{Z}/3 = \frac{\mathbb{Z}}{3\mathbb{Z}}`.
:::

Now, we want to mimic this definition in a general _abelian_ category $`\mathcal{A}`.
So, let's write down a criterion for when $`A \xrightarrow{f} B \xrightarrow{g} C` is exact.
First, we had better have that $`g \circ f = 0`, which encodes the fact that $`\mathrm{img}(f) \subseteq \ker(g)`.
Since $`A \twoheadrightarrow \mathrm{Img}\, f` is epic in an abelian category, one deduces there is a _unique_ map $`\mathrm{Img}\, f \to \mathrm{Ker}\, g`, and we require that it be an isomorphism.
In short,

:::DEFINITION
Let $`\mathcal{A}` be an abelian category.
The sequence $$`\dots \to A_{n-1} \xrightarrow{f_n} A_n \xrightarrow{f_{n+1}} A_{n+1} \to \dots`
is *exact* at $`A_n` if $`f_{n+1} \circ f_n = 0` and the canonical map $`\mathrm{Img}\, f_n \to \mathrm{Ker}\, f_{n+1}` is an isomorphism.
The entire sequence is exact if it is exact at each $`A_i`.
(For finite sequences we don't impose the condition on the very first and very last object.)
:::

:::figure "figures/category-theory/exact-def.svg"
Exactness at $`B`: the canonical map $`\mathrm{Img}\, f \to \mathrm{Ker}\, g` is an isomorphism.
:::

:::EXERCISE
Show that, as before, $`0 \to A \to B` is exact $`\iff` $`A \to B` is monic.
:::

# The Freyd–Mitchell embedding theorem

We now introduce the Freyd–Mitchell embedding theorem, which essentially says that any abelian category can be realized as a concrete one.

:::DEFINITION
A category is *small* if its objects form a set (as opposed to a class), i.e. there is a "set of all objects in $`\mathcal{A}`".
For example, $`\mathsf{Set}` is not small because there is no set of all sets.
:::

:::THEOREM "Freyd–Mitchell embedding theorem"
Let $`\mathcal{A}` be a small abelian category.
Then there exists a ring $`R` (with $`1` but possibly non-commutative) and a full, faithful, exact functor onto the category of left $`R`-modules.
:::

Here a functor is *exact* if it preserves exact sequences.
This theorem is good because it means

:::MORAL
You can basically forget about all the weird definitions that work in any abelian category.
:::

Any time you're faced with a statement about an abelian category, it suffices to just prove it for a "concrete" category where injective/surjective/kernel/image/exact/etc. agree with your previous notions.

:::REMARK
The "small" condition is a technical obstruction that requires the objects of $`\mathcal{A}` to actually form a set.
I'll ignore this distinction, because one can almost always work around it by doing enough set-theoretic technicalities.
:::

For example, let's prove:

:::LEMMA "Short five lemma"
In an abelian category, consider a commutative diagram whose top and bottom rows are the exact sequences $`0 \to A \xrightarrow{p} B \xrightarrow{q} C \to 0` and $`0 \to A' \xrightarrow{p'} B' \xrightarrow{q'} C' \to 0`, joined by vertical maps $`\alpha \colon A \to A'`, $`\beta \colon B \to B'`, $`\gamma \colon C \to C'`.
If $`\alpha` and $`\gamma` are isomorphisms, then so is $`\beta`.
:::

:::figure "figures/category-theory/short-five-ladder.svg"
A morphism of short exact sequences, with $`\alpha` and $`\gamma` isomorphisms.
:::

::::PROOF
We prove that $`\beta` is epic (with a similar proof to get monic).
By the embedding theorem we can treat the category as $`R`-modules over some $`R`.
This lets us do a so-called "diagram chase" where we move elements around the picture, using the concrete interpretation of our category as $`R`-modules.

Let $`b'` be an element of $`B'`.
Then $`q'(b') \in C'`, and since $`\gamma` is surjective, we have a $`c` such that $`\gamma(c) = q'(b')`, and finally a $`b \in B` such that $`q(b) = c`.

:::figure "figures/category-theory/five-chase-1.svg"
Chasing $`b \in B` to $`c \in C` and across to $`b' \in B'`.
:::
Now, it is not necessarily the case that $`\beta(b) = b'`.
However, since the diagram commutes we at least have that $`q'(b') = q'(\beta(b))`, so $`b' - \beta(b) \in \mathrm{Ker}\, q' = \mathrm{Img}\, p'`, and there is an $`a' \in A'` such that $`p'(a') = b' - \beta(b)`; use $`\alpha` now to lift it to $`a \in A`.

:::figure "figures/category-theory/five-chase-2.svg"
Producing $`a \in A` whose image corrects $`\beta(b)` to hit $`b'`.
:::
Then, we have $$`\beta(b + p(a)) = \beta b + \beta p a = \beta b + p' \alpha a = \beta b + (b' - \beta b) = b'`
so $`b' \in \mathrm{Img}\, \beta`, which completes the proof that $`\beta` is surjective.
::::

In general, proofs in the style above (whether or not they use the embedding theorem) are sometimes referred to by the name *diagram chasing*.
I'm not sure there's an exact definition for this term, but the following quote is due to Aluffi:

:::quote
Proving the snake lemma (a problem at the end of this chapter) is something that should not be done in public, and it is notoriously useless to write down the details of the verification for others to read: the details are all essentially obvious, but they lead quickly to a notational quagmire.
Such proofs are collectively known as the sport of diagram chase, best executed by pointing several fingers at different parts of a diagram on a blackboard, while enunciating the elements one is manipulating and stating their fate.
:::

# Breaking long exact sequences

:::PROTOTYPE
First isomorphism theorem.
:::

In fact, it turns out that any exact sequence breaks into short exact sequences.
This relies on:

:::PROPOSITION "\"First isomorphism theorem\" in abelian categories"
Let $`A \xrightarrow{f} B` be an arrow of an abelian category.
Then there is an exact sequence $$`0 \to \mathrm{Ker}\, f \xrightarrow{\ker f} A \xrightarrow{\mathrm{img}\, f} \mathrm{Img}\, f \to 0.`
:::

:::EXAMPLE "Two familiar instances"
Let's analyze this theorem in our two examples of abelian categories:

1. In the category of abelian groups, this is basically the first isomorphism theorem.
2. In the category $`\mathsf{Vect}_k`, this amounts to the rank-nullity theorem.
:::

Thus, any exact sequence can be broken into short exact sequences, by splicing at the objects $`C_k = \mathrm{img}\, f_{k-1} = \ker f_k` for every $`k`; each three-term stretch $`0 \to C_k \to A_k \to C_{k+1} \to 0` is then short exact.

:::figure "figures/category-theory/les-woven.svg"
A long exact sequence woven from the short exact sequences $`0 \to C_k \to A_k \to C_{k+1} \to 0`.
:::

# Problems

:::PROBLEM "Four lemma"
In an abelian category, consider a commutative diagram with exact rows $`A \xrightarrow{p} B \xrightarrow{q} C \xrightarrow{r} D` (top) and $`A' \xrightarrow{p'} B' \xrightarrow{q'} C' \xrightarrow{r'} D'` (bottom), joined by vertical maps $`\alpha, \beta, \gamma, \delta`.
Prove that if $`\alpha` is epic, and $`\beta` and $`\delta` are monic, then $`\gamma` is monic.
:::

:::figure "figures/category-theory/four-lemma.svg"
The four lemma: exact rows joined by $`\alpha, \beta, \gamma, \delta`.
:::

:::PROBLEM "Five lemma"
In an abelian category, consider a commutative diagram with exact rows $`A \to B \to C \to D \to E` and $`A' \to B' \to C' \to D' \to E'`, joined by vertical maps $`\alpha, \beta, \gamma, \delta, \varepsilon`.
Suppose $`\beta` and $`\delta` are isomorphisms, $`\alpha` is epic, and $`\varepsilon` is monic.
Prove that $`\gamma` is an isomorphism.
:::

:::figure "figures/category-theory/five-lemma.svg"
The five lemma: exact rows joined by $`\alpha, \beta, \gamma, \delta, \varepsilon`.
:::

:::PROBLEM "Snake lemma"
In an abelian category, consider a commutative diagram with exact rows $`A \xrightarrow{f} B \xrightarrow{g} C \to 0` (top) and $`0 \to A' \xrightarrow{f'} B' \xrightarrow{g'} C'` (bottom), joined by vertical maps $`a, b, c`.
Prove that there is an exact sequence $$`\mathrm{Ker}\, a \to \mathrm{Ker}\, b \to \mathrm{Ker}\, c \to \mathrm{Coker}\, a \to \mathrm{Coker}\, b \to \mathrm{Coker}\, c.`
:::

:::figure "figures/category-theory/snake-setup.svg"
The snake lemma setup: two exact rows joined by $`a, b, c`.
:::

:::PROBLEM "An additive category that is not abelian"
Consider a category, where:

- the objects are pairs of abelian groups $`(B, A)` where $`A` is a subgroup of $`B`.
- the morphisms $`(B, A) \to (B', A')` are maps $`f \colon B \to B'` where $`f(A) \subseteq A'`.

This category can be equivalently viewed as the category of short exact sequences $`0 \to A \to B \to B/A \to 0` of abelian groups.

Show that the arrow $`(X, 0) \to (X, X)` is monic and epic, but not an isomorphism.
Conclude that the category is not abelian.
:::

# Formalization

:::LEANCOMPANION
:::

## Zero objects, kernels, cokernels, and images

The three ingredients are typeclasses on a category: {name}`CategoryTheory.Limits.HasZeroObject` for the object $`0`, {name}`CategoryTheory.Limits.HasZeroMorphisms` for the distinguished $`0 \colon A \to B`, and {name}`CategoryTheory.Limits.kernel` and {name}`CategoryTheory.Limits.cokernel` for the (co)equalizers against that zero morphism.
The image built here as $`\mathrm{Ker}(\mathrm{coker}\, f)` is exactly {name}`CategoryTheory.Abelian.image`.

The defining property of the kernel is that its inclusion $`\ker f` composes with $`f` to give the zero morphism.

```lean
example (C : Type*) [Category C] [HasZeroMorphisms C] {A B : C} (f : A ⟶ B)
    [HasKernel f] : kernel.ι f ≫ f = 0 :=
  kernel.condition f
```

Dually, $`f` composed with the projection to its cokernel vanishes.
Prove it; `cokernel.condition` does the work.

```lean
example (C : Type*) [Category C] [HasZeroMorphisms C] {A B : C} (f : A ⟶ B)
    [HasCokernel f] : f ≫ cokernel.π f = 0 := by
  sorry
```

## Additive and abelian categories

The "you can add morphisms" content is {name}`CategoryTheory.Preadditive`, an abelian-group structure on each hom-set with bilinear composition; an additive category is this together with a zero object and binary products.
The full package with kernels, cokernels, and the image factorization is {name}`CategoryTheory.Abelian`, and $`\mathsf{Mod}_R` is the guiding instance.
Bilinearity of composition means that precomposing a sum is the sum of the precompositions.

```lean
example (C : Type*) [Category C] [Preadditive C] {A B D : C}
    (f f' : A ⟶ B) (g : B ⟶ D) : (f + f') ≫ g = f ≫ g + f' ≫ g := by
  simp
```

The proposition above characterized isomorphisms as the maps that are both monic and epic.
One half of that holds in every abelian category: a map that is monic and epic is an isomorphism.
The lemma `isIso_of_mono_of_epi` does the work; prove it.

```lean
example (C : Type*) [Category C] [Abelian C] {A B : C} (f : A ⟶ B)
    [Mono f] [Epi f] : IsIso f := by
  sorry
```

## Exact sequences

A composable pair $`A \xrightarrow{f} B \xrightarrow{g} C` with $`g \circ f = 0` is a {name}`CategoryTheory.ShortComplex`; the predicate {name}`CategoryTheory.ShortComplex.Exact` is exactly "the canonical map from the image to the kernel is an isomorphism", and {name}`CategoryTheory.ShortComplex.ShortExact` adds that the outer maps are monic and epic — the categorical $`0 \to A \to B \to C \to 0`.
The compatibility built into a short complex is that its two maps compose to zero.

```lean
example (C : Type*) [Category C] [HasZeroMorphisms C] (S : ShortComplex C) :
    S.f ≫ S.g = 0 :=
  S.zero
```

The exercise above showed that $`0 \to A \to B` is exact exactly when $`A \to B` is monic.
When the first map of a short complex is zero, exactness of the complex is precisely monicity of the second map.
That equivalence is `ShortComplex.exact_iff_mono`, applied to `hf`.

```lean
example (C : Type*) [Category C] [Abelian C] (S : ShortComplex C)
    (hf : S.f = 0) : S.Exact ↔ Mono S.g := by
  sorry
```

## The Freyd–Mitchell embedding theorem

The full embedding theorem is {name}`CategoryTheory.Abelian.freyd_mitchell`: for any abelian category it produces a ring, together with a full, faithful, exact functor into that ring's modules.
The exactness is packaged as preservation of finite limits and finite colimits, {name}`CategoryTheory.Limits.PreservesFiniteLimits` and {name}`CategoryTheory.Limits.PreservesFiniteColimits`.
That existence statement is witnessed by a concrete embedding {name}`CategoryTheory.Abelian.FreydMitchell.functor` into modules over the ring {name}`CategoryTheory.Abelian.FreydMitchell.EmbeddingRing`, which carries all four properties as instances.

```lean
noncomputable example (C : Type*) [Category C] [Abelian C] :
    C ⥤ ModuleCat (Abelian.FreydMitchell.EmbeddingRing C) :=
  Abelian.FreydMitchell.functor C

example (C : Type*) [Category C] [Abelian C] :
    (Abelian.FreydMitchell.functor C).Full := inferInstance
```

Faithfulness is what makes the phrase "and therefore the two maps are equal" at the end of a chase legitimate: two morphisms that become equal after embedding into modules were already equal.

```lean
example (C : Type*) [Category C] [Abelian C] {A B : C} (f g : A ⟶ B)
    (h : (Abelian.FreydMitchell.functor C).map f
        = (Abelian.FreydMitchell.functor C).map g) : f = g :=
  (Abelian.FreydMitchell.functor C).map_injective h
```

Because the embedding is full and faithful it reflects both monomorphisms and epimorphisms, so checking that a map is monic — or epic — can be done on its image in modules, where it means injective or surjective.

```lean
example (C : Type*) [Category C] [Abelian C] {A B : C} (f : A ⟶ B)
    (h : Mono ((Abelian.FreydMitchell.functor C).map f)) : Mono f :=
  (Abelian.FreydMitchell.functor C).mono_of_mono_map h
```

Dually, the same functor reflects epimorphisms via `epi_of_epi_map`.
If the image of $`f` is epic then $`f` itself is epic.

```lean
example (C : Type*) [Category C] [Abelian C] {A B : C} (f : A ⟶ B)
    (h : Epi ((Abelian.FreydMitchell.functor C).map f)) : Epi f :=
  (Abelian.FreydMitchell.functor C).epi_of_epi_map h
```

A chase also needs the embedding to send the zero morphism to the zero morphism, so that "starting from an element that maps to zero" survives the translation.

```lean
example (C : Type*) [Category C] [Abelian C] (A B : C) :
    (Abelian.FreydMitchell.functor C).map (0 : A ⟶ B) = 0 :=
  (Abelian.FreydMitchell.functor C).map_zero A B
```

There is also a lighter-weight route that stays inside the abstract category: {name}`CategoryTheory.Abelian.Pseudoelement` lets you chase "elements" of objects in _any_ abelian category, without naming the embedding at all.
A morphism $`f` acts on pseudoelements through {name}`CategoryTheory.Abelian.Pseudoelement.pseudoApply`, and chasing through a composite applies each map in turn.

```lean
open CategoryTheory.Abelian.Pseudoelement in
example (C : Type*) [Category C] [Abelian C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (a : Abelian.Pseudoelement A) :
    pseudoApply (f ≫ g) a = pseudoApply g (pseudoApply f a) :=
  comp_apply f g a
```

Every diagram chase relies on each map sending the zero pseudoelement to the zero pseudoelement.
Prove it; `apply_zero` does the work.

```lean
open CategoryTheory.Abelian.Pseudoelement in
example (C : Type*) [Category C] [Abelian C] {A B : C} (f : A ⟶ B) :
    pseudoApply f (0 : Abelian.Pseudoelement A) = 0 := by
  sorry
```

## Breaking long exact sequences

The first isomorphism theorem splices a map into the short exact sequence $`0 \to \mathrm{Ker}\, f \to A \to \mathrm{Img}\, f \to 0`.
Mathlib does not package this categorical statement under a single name, but a {name}`CategoryTheory.ShortComplex.ShortExact` records exactly the data at the two ends: its first map is monic and its second map is epic.

```lean
example (C : Type*) [Category C] [Preadditive C] {S : ShortComplex C}
    (hS : S.ShortExact) : Mono S.f := hS.mono_f
```

Dually, the last map of a short exact sequence is epic.
Prove it; `hS.epi_g` does the work.

```lean
example (C : Type*) [Category C] [Preadditive C] {S : ShortComplex C}
    (hS : S.ShortExact) : Epi S.g := by
  sorry
```
