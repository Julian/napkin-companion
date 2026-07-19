import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PicardGroup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Line bundles" =>

%%%
file := "Line-bundles"
%%%

# Overview

You might have heard about line bundles, which is somehow "a set $`L` with a map $`\pi \colon L \to X` where the preimage of each point is a line".
And then, in the algebraic geometry section, you come across the concept of "section" which appears to be just a function.

That sounds reasonable, but you may ask, "so what? Isn't it then just another complex manifold which has one more dimension than $`X`? Why not just study complex manifold?"

It's true, but there are more structures on a line bundle:

- You can take the product of two line bundles, which somehow "add up the twists" of both line bundles.
- A section is not just a function — you can think of a section as the graph of a function in the special case that the "graph paper" itself is flat, but if it is curved like a Möbius strip, you will see that there is no way to assign a "function value" to each point of the "graph paper" — a situation which we will call "the line bundle is not trivial".

In other words, a line bundle vastly generalizes the "space of the graph of a function".

Later on, you will see a deep hidden connection between line bundles and linearly equivalent classes of divisors, and how they are all linked by the so-called Picard group.

# Definition

Let $`X` be a Riemann surface.

In this section, we will view $`X` as just a curve — that is, a $`1`-dimensional object instead of a $`2`-dimensional object — because:

- It is easier to visualize things when they can be embedded in $`3`-dimensional space.
  (Try to draw the graph of … with both real and complex part, and you will see what I mean!)
- Since all of our functions of interest are analytic, the behavior of a function elsewhere is determined by its value on the real axis.

Looking only at the real part can makes some intuition slipped however — for example, it is possible to overlook that the circle $`x^2 + y^2 = 1` and the hyperbola $`x^2 = 1 + y^2` cuts out Riemann surfaces in $`\mathbb{C}^2` of the same shape, or that the function $`\frac{1}{x^2 + 1}` has a pole at $`x = \pm i`.
So, be careful.

:::DEFINITION
A *line bundle* $`L` is a set, together with:

- A projection map $`\pi \colon L \to X`,
- An open cover $`\{ U_i \}` of $`X`,
- For each $`U_i`, a *line bundle chart* $`\phi \colon \pi^{\mathrm{pre}}(U) \to \mathbb{C} \times U` that bijectively maps each point in $`\pi^{\mathrm{pre}}(p)` to a point in $`\mathbb{C} \times p`,
- For two open sets $`U_1` and $`U_2`, the *transition function* $`\phi_2 \circ \phi_1^{-1} \colon \mathbb{C} \times U_1 \to \mathbb{C} \times U_2` must be a _$`\mathbb{C}`-vector space isomorphism_ restricted to $`\mathbb{C} \times p \to \mathbb{C} \times p` for each point $`p \in U_1 \cap U_2`, and the scaling factor must be an analytic function on $`U_1 \cap U_2`.
:::

:::REMARK "Warning"
Typically, we draw a graph of the function $`f(x)` by the set of points $`(x, y)` where $`y = f(x)`.

This time, we use the notation in {cite}`ref:miranda` — the target of a line bundle chart is $`\mathbb{C} \times U` instead of $`U \times \mathbb{C}` — so if we consider a section the generalization of a function, the coordinate would look like $`(y, x)` instead.
:::

The definition is dense, but essentially:

:::MORAL
A line bundle is a set with a line bundle structure, consisting of an analytic structure and a $`1`-dimensional vector space structure.
:::

The transition maps is simply to weld the pieces of the line bundle together, just like how they welded pieces of a Riemann surface in the chapter on complex structures.

Another definition, we will explain this one later.

:::DEFINITION "Sections of a line bundle"
Let $`L` be a line bundle.
A *section* on an open set $`U` is a map $`f \colon U \to L` such that $`\pi \circ f` is the identity map on $`U`.

We call a section $`f \colon X \to L` a *global section*.

The section $`f \colon U \to L` is an *analytic section* if for every $`U_1 \subseteq U` such that there is a line bundle chart $`\phi \colon \pi^{\mathrm{pre}}(U_1) \to \mathbb{C} \times U_1`, then $`\phi \circ f \restriction_{U_1} \colon U_1 \to \mathbb{C} \times U_1` is analytic.
:::

We will see this definition later on in algebraic geometry, as the sections of a presheaf.

:::REMARK
In most books, they will first define what a sheaf is, then instead of "analytic section", they say "a section of the sheaf of analytic functions" (or regular functions, etc.)
:::

# Visualizing a line bundle

Just as how you can keep all the information of the Riemann sphere $`\mathbb{C}_\infty` in your head at once just by visualizing a sphere (with the analytic structure viewed as some "compatible grids" on the surface), you should also be able to keep all the information of a line bundle in your head at once — at least in the simplest cases.

First, we visualize $`\mathbb{C} \times X` where $`X = \mathbb{C}`.
Looking at only the real parts, it looks like a plane.

:::figure "figures/riemann-surfaces/lb-plane.svg"
:::

As a line bundle, the preimage of each point is a line.

:::figure "figures/riemann-surfaces/lb-lines.svg"
:::

:::QUESTION
In symbols, what subset of $`\mathbb{C} \times X` does a vertical line correspond to?
:::

They are not just disparate lines however — there are two more structures.
First one is a vector space structure — of course the dimension of $`\mathbb{C}` as a $`\mathbb{C}`-vector space is $`1`.
We can visualize it by marking the points $`1, 2, 3, \dots` on the line.

:::figure "figures/riemann-surfaces/lb-dots.svg"
:::

The other structure is that the lines must "smoothly varies" as $`p` varies over $`X`.
We visualize this by drawing, well, a grid.

:::figure "figures/riemann-surfaces/lb-grid.svg"
:::

:::QUESTION
How does the picture of the grid correspond to the formal definition of a line bundle chart?
(Hint: take the preimage of the vertical lines $`x = c` and the horizontal lines $`y = c` with respect to the line bundle chart $`\phi \colon L \to \mathbb{C} \times U`, where $`U \subseteq X`, then use the analytic structure on $`X` to identify open subsets of $`U` with open subsets of $`\mathbb{C}`.)
:::

So far, nothing surprising — this is just the usual grid graph, where we can draw functions on it like $`y = x^2-1`, and a function is analytic if it is analytic with respect to the grid.

:::figure "figures/riemann-surfaces/lb-section.svg"
:::

Of course, instead of a function, we call this a _section_.
This particular section is in fact analytic, as you would expect.

Let us take a look at which "grids" represent the same line bundle structure.
For this part, we will look at $`\{ z : \mathbb{C} \mid |z-3| < 2 \}`, its real part being $`(1, 5)`.

:::figure "figures/riemann-surfaces/lb-chart1.svg"
:::

If we apply an analytic reparametrization on the segment $`(1, 5)` — for example let $`t = 25/x`, then the grid becomes like the following.
It still represents the same line bundle structure — in other words, the two charts are compatible.

:::figure "figures/riemann-surfaces/lb-chart2.svg"
:::

If we rescale the vertical direction by an analytically-varying function, it still represents the same line bundle structure.

:::figure "figures/riemann-surfaces/lb-chart3.svg"
:::

However, if we rescale the vertical direction by something that is not linear, the vector space structure will be changed.
The following grid _does not_ represent the same line bundle structure:

:::figure "figures/riemann-surfaces/lb-chart4.svg"
:::

Intuitively, this makes sense — in a _vector space_, you can add two elements together and get another element — in our case, if $`a, b : L` such that $`\pi(a) = \pi(b)`, we can compute $`c = a + b` and get another element $`c : L` with $`\pi(c) = \pi(a) = \pi(b)`.
If we rescale the vertical direction non-linearly, the element $`c` will be changed.

Finally, don't forget that $`L` still has an analytic structure — even though a section isn't necessarily a function, we are still able to say when a section is analytic.

:::QUESTION
Verify that everything explained above matches the formal definition.
(This is important! Fuzzy pictures won't help you to understand the concepts; and if your intuition is incomplete or inaccurate, you will have a lot of trouble understanding the subsequent parts.)
:::

So far, everything just looks like a graph paper, on which a section looks just like a function.{margin}[As warned above, "graph coordinate" is written $`(y, x)`.]
Let us consider a more complicated space $`X` — the Riemann sphere.

Because we are looking at the real part only, so once again, $`\mathbb{C}_\infty` looks like just a circle.

:::figure "figures/riemann-surfaces/cinf.svg"
:::

As before, we let $`z` and $`t` parametrize the points on the surface, with $`t = \frac{1}{z}` wherever both are defined.

Still, we need two dimensions to embed a circle.
So, the real part of $`\mathbb{C} \times \mathbb{C}_\infty` may looks something like the following:

:::figure "figures/riemann-surfaces/cxcinf.svg"
:::

The grid lines are drawn, and the origin $`z = 0`, is marked with a dot.
The vertical lines mark the position $`z = 0`, $`z = \frac{1}{2}`, $`z = 1`, $`z = \frac{3}{2}`, ….

On the opposite side, we may have something like the following.
The vertical lines mark the position $`t = 0`, $`t = \frac{1}{2}`, $`t = 1`, $`t = \frac{3}{2}`, ….

:::figure "figures/riemann-surfaces/cxcinf2.svg"
:::

:::QUESTION
Check that, on $`\mathbb{C} \times U` for any open set $`U \subseteq \mathbb{C}_\infty` that contains neither $`0` nor $`\infty`, the two line bundle charts above define the same line bundle structure.
(What are the transition functions?)
:::

So, we have the so-called trivial line bundle $`\mathbb{C} \times \mathbb{C}_\infty`.

As promised, there are also nontrivial line bundles here.

First, recall from the section above: over any open set $`U` that contains neither $`0` nor $`\infty`, we can consider another line bundle chart that scales the vertical direction by a factor of $`z`, this induces the same line bundle structure on $`U`.

:::figure "figures/riemann-surfaces/lb-twist.svg"
:::

:::QUESTION
Let $`\phi_p` and $`\phi_g` be the line bundle charts corresponding to the purple and green grid, respectively.
Verify that if a point $`q : L` satisfies $`\phi_p(q) = (y, z)` for $`z \notin \{ 0, \infty \}`, then $`\phi_g(q) = (\frac{y}{z}, z)`.
:::

Now — note that the trivial line bundle $`\mathbb{C} \times \mathbb{C}_\infty` above can be seen as welding the two pieces together, such that the purple line $`(y, z)` gets welded to the red line $`(y, t)` for each $`y`.
There is nothing that restricts us to that specific welding method, however — this time around, we will try to weld the green line $`(\frac{y}{z}, z)` to the red line $`(y, t)` for each $`y`.

The thing will look like this.
It looks quite complicated, so this time 4 views are shown.

:::figure "figures/riemann-surfaces/cxcinf3.svg"
:::

The cylinder this time is only for illustrative purpose.
Let us see what is going on.

- First, near the purple and the red point, the graph lines looks like our usual situation.

  Note that because $`t = \frac{1}{z}`, looking from outside, the red coordinate lines will looks flipped.
- On the positive side ($`z > 0` and $`t > 0`), no problem — we just need to squeeze the purple lines closer together — as depicted in the figure.
- On the negative side, however — note that the green line $`(\frac{y}{z}, z)` moves _downwards_ when $`y` increases, so we will need to "twist the graph paper" for it to go up.

  In the figure, this is depicted as a singularity where all the horizontal lines intersect, but in reality, you should think of it as we twisting the "graph paper" by 180 degrees and weld it to the other part.

This is a Möbius strip!

Thus, it appears to be obvious that this line bundle is not isomorphic to the trivial one, whatever "isomorphic" might mean.

:::QUESTION
Check that what we did above makes sense when $`y`, $`z` and $`t` are not real — in particular, $`\mathbb{C} \setminus \{ 0 \}` is a connected set, unlike $`\mathbb{R} \setminus \{ 0 \}`.
You probably won't be able to visualize the "graph paper" this time (it is $`4`-dimensional!), so you will have to keep your intuition confined in the real part and use algebra for the rest.
:::

# Morphisms between line bundles

In order to formally define what it means for two line bundles to be isomorphic, we need to be able to define morphisms.
It is exactly what you expect — it must respect the line bundle structure (that is, the vector space structure and the analytic structure) on $`L_1` and $`L_2`.

:::DEFINITION
Let $`\pi_1 \colon L_1 \to X` and $`\pi_2 \colon L_2 \to X` be line bundles.
A line bundle morphism $`\alpha \colon L_1 \to L_2` is a set morphism such that:

- $`\pi_2 \circ \alpha = \pi_1`, and
- if $`\phi_1 \colon \pi_1^{\mathrm{pre}}(U_1) \to \mathbb{C} \times U_1` and $`\phi_2 \colon \pi_2^{\mathrm{pre}}(U_2) \to \mathbb{C} \times U_2` are line bundle charts, then the composition $$`\phi_2 \circ \alpha \circ \phi_1^{-1} \colon \mathbb{C} \times (U_1 \cap U_2) \to \mathbb{C} \times (U_1 \cap U_2)` has the form $`(s, p) \mapsto (f(p) \cdot s, p)` where $`f` is analytic on $`U_1 \cap U_2`.
:::

:::EXERCISE
The function $`f(p)` above must be nonzero for all $`p \in U_1 \cap U_2`.
Why?
(Hint: invert the function by swapping the role of $`\phi_1` and $`\phi_2`.)
:::

:::QUESTION
Check that the above definition is the equivalent to the following: $`\alpha` is a line bundle morphism if and only if

- it maps a point $`q \in \pi_1^{\mathrm{pre}}(x)` to some point $`\alpha(q) \in \pi_2^{\mathrm{pre}}(x)` (that is, each fiber gets mapped to the corresponding fiber), and
- for every analytic section $`s \colon U \to L_1` on open set $`U \subseteq X`, then $`\alpha(s)` is an analytic section $`s \colon U \to L_2`.
:::

:::EXAMPLE
Let $`X = \mathbb{C}`.
Then $`\alpha \colon \mathbb{C} \times X \to \mathbb{C} \times X` by $`\alpha(y, x) = (y \cdot x^2, x)` is a line bundle homomorphism.

This line bundle homomorphism is not an isomorphism, because every point $`(y, 0)` gets mapped to $`(0, 0)`.
:::

The definition of line bundle isomorphism is what you would expect.

:::DEFINITION "Isomorphism of line bundles"
Two line bundles $`L_1` and $`L_2` are *isomorphic* if there are line bundle isomorphisms $`\alpha \colon L_1 \to L_2` and $`\beta \colon L_2 \to L_1` that are inverse of each other.
:::

# Relation to invertible sheaves

We close with a preview whose full story belongs to the algebraic geometry part (we haven't defined a sheaf yet, so a preview is all it can be).

Fix a line bundle $`\pi \colon L \to X`, and for each open set $`U \subseteq X` write $$`\mathcal{L}(U) = \{ \text{analytic sections } U \to L \}.`
Two features of this assignment stand out.

- Sections can be restricted to smaller open sets, and are determined by their restrictions to the pieces of any open cover — this "local-to-global" bookkeeping is exactly what the word *sheaf* will axiomatize.
- Over each $`U`, an analytic section can be multiplied by an analytic _function_ $`U \to \mathbb{C}` (scale each value in its fiber).
  So $`\mathcal{L}(U)` is a module over the analytic functions on $`U` — and locally, over a $`U` with a line bundle chart, sections _are_ just analytic functions, so the module is free of rank $`1`.

A sheaf of modules which is locally free of rank $`1` in this sense is called an *invertible sheaf*, and the assignment $`L \mapsto \mathcal{L}` turns out to be a bijection between line bundles up to isomorphism and invertible sheaves up to isomorphism.
The name "invertible" comes from the product structure mentioned in the overview: the product of line bundles "adds the twists", the trivial bundle is the identity, and every line bundle has an inverse (twist the other way), so the isomorphism classes form a group — the *Picard group* of $`X`.
The connection promised with divisors also goes through this group: a divisor $`D` determines the invertible sheaf whose sections over $`U` are the meromorphic functions with $`\operatorname{Div}(f) \geq -D` on $`U` — the sheafy upgrade of the space $`L(D)` from the previous chapter — and linearly equivalent divisors give isomorphic sheaves.

# Formalization

:::LEANCOMPANION
:::

## Definition

Everything in the definition except the word *analytic* is present.
The total space of a bundle over a base $`B` with model fiber $`F` is `Bundle.TotalSpace F E`, and it carries a projection `TotalSpace.proj` sending each point to the base point below it.

```lean
example (B : Type*) (E : B → Type*) (x : B) (v : E x) :
    (Bundle.TotalSpace.mk x v : Bundle.TotalSpace ℂ E).proj = x := rfl
```

A line bundle chart is a `Trivialization ℂ π` — a homeomorphism from `π ⁻¹' U` to `U × ℂ` respecting the projection.
Mathlib sides with the "graph paper" convention, base coordinate first, against {cite}`ref:miranda` and the convention above.

```lean
example (B F Z : Type*) [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace Z] (p : Z → B) : Type _ := Bundle.Trivialization F p
```

The requirement that the fiberwise transitions be linear in the fiber, together with the continuity of the scaling factors, is packaged by `VectorBundle ℂ F E`; the coordinate change induced by two charts is `Trivialization.coordChangeL`.
Its model example is the trivial line bundle `Bundle.Trivial B ℂ`, whose fibers are each a single copy of $`\mathbb{C}`.

```lean
example (B : Type*) [TopologicalSpace B] :
    VectorBundle ℂ ℂ (Bundle.Trivial B ℂ) := inferInstance
```

The transition function welding the trivial bundle to itself is the identity — there is no twist.

```lean
example (B : Type*) [TopologicalSpace B] (b : B) :
    (Bundle.Trivial.trivialization B ℂ).coordChangeL ℂ
        (Bundle.Trivial.trivialization B ℂ) b
      = ContinuousLinearEquiv.refl ℂ ℂ :=
  Bundle.Trivial.trivialization.coordChangeL (B := B) (F := ℂ) b
```

The gap is the last word of the definition.
These bundles come in topological and smooth flavors, but there is no *holomorphic* vector bundle yet, and that difference is precisely where all of this chapter's content lives — so the exercises below stay in the topological world that is present.

The zero section sends each base point to the zero of the fiber above it; check that it does land back over the point it came from.

```lean
example (B : Type*) [TopologicalSpace B] (x : B) :
    (Bundle.zeroSection ℂ (Bundle.Trivial B ℂ) x).proj = x := by
  sorry
```

A chart respects the projection: reading off the base coordinate of `e z` recovers `p z` on the chart's source.

```lean
example (B F Z : Type*) [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace Z] (p : Z → B) (e : Bundle.Trivialization F p) (z : Z)
    (hz : z ∈ e.source) : (e z).1 = p z := by
  sorry
```

## Visualizing a line bundle

The trivial line bundle `Bundle.Trivial ℂ ℂ` really is "graph paper": its total space is just the product $`\mathbb{C} \times \mathbb{C}`, exactly the plane in the pictures.

```lean
example (B F : Type*) :
    Bundle.TotalSpace F (Bundle.Trivial B F) ≃ B × F :=
  Bundle.TotalSpace.toProd B F
```

The twisted bundle built by welding with a factor of $`z` — the Möbius strip over the Riemann sphere — has no direct expression here, since the holomorphic bundle theory it needs is absent.
Working inside the identification above instead, check that its first coordinate reads off the base point.

```lean
example (B F : Type*) (z : Bundle.TotalSpace F (Bundle.Trivial B F)) :
    (Bundle.TotalSpace.toProd B F z).1 = z.proj := by
  sorry
```

## Morphisms between line bundles

A morphism looks locally like $`(s, p) \mapsto (f(p) \cdot s, p)`.
Fiberwise, over a single point, it is multiplication by the scalar $`f(p)`, that is, a continuous linear map $`\mathbb{C} \to \mathbb{C}`.

```lean
noncomputable example (c : ℂ) : ℂ →L[ℂ] ℂ :=
  c • ContinuousLinearMap.id ℂ ℂ
```

The prose example's fiber maps are $`x \mapsto (\text{multiply by } x^2)`.

```lean
noncomputable example : ℂ → (ℂ →L[ℂ] ℂ) :=
  fun x => (x ^ 2) • ContinuousLinearMap.id ℂ ℂ
```

Such a fiber map is invertible exactly when its scalar is nonzero — the reason the morphism above degenerates at $`x = 0`.

```lean
example (c : ℂ) (hc : c ≠ 0) :
    IsUnit (c • ContinuousLinearMap.id ℂ ℂ) := by
  refine ⟨⟨c • ContinuousLinearMap.id ℂ ℂ,
    c⁻¹ • ContinuousLinearMap.id ℂ ℂ, ?_, ?_⟩, rfl⟩ <;>
    ext <;> simp [mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
```

The exercise from the section — that $`f(p)` must be nonzero for a morphism to be invertible — is, fiberwise, the statement that a scalar of $`\mathbb{C}` is a unit exactly when it is nonzero.

```lean
example (c : ℂ) : IsUnit c ↔ c ≠ 0 := by
  sorry
```

## Relation to invertible sheaves

The Picard group is present in its commutative-algebra incarnation: `CommRing.Pic R` is the group of invertible modules over a ring $`R`.

```lean
example (R : Type*) [CommRing R] : Type _ := CommRing.Pic R

noncomputable example (R : Type*) [CommRing R] :
    CommGroup (CommRing.Pic R) := inferInstance
```

`ClassGroup.equivPic` relates it to the class group of a domain.

```lean
noncomputable example (R : Type*) [CommRing R] [IsDomain R] :
    ClassGroup R ≃* CommRing.Pic R := ClassGroup.equivPic R
```

None of this is connected to analytic line bundles over Riemann surfaces, whose story stops at the smooth vector bundles above.
Still, the algebraic Picard group already sees "every line bundle is trivial" over the nicest bases: over $`\mathbb{Z}`, a unique-factorization domain, it collapses to a single element.

```lean
example : Subsingleton (CommRing.Pic ℤ) := by
  sorry
```
