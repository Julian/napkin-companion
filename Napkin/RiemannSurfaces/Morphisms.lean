import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Napkin.Missing.RamifiedMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing

open scoped Manifold Topology

set_option pp.rawOnError true

#doc (Manual) "Morphisms between Riemann surfaces" =>

%%%
file := "Riemann-morphisms"
%%%

# Definition

The definition is what we would expect — since a Riemann surface's main feature is a complex structure, a map $`f \colon \mathbb{C} \to \mathbb{C}` is a morphism between Riemann surfaces if and only if it is holomorphic.

:::DEFINITION "Morphism between Riemann surfaces"
Let $`X` and $`Y` be Riemann surfaces.
A mapping $`f \colon X \to Y` is *holomorphic* at $`p \in X` if and only if there exist charts $`\phi_1 \colon U_1 \to E_1` on $`X` with $`p \in U_1` and $`\phi_2 \colon U_2 \to E_2` on $`Y` with $`f(p) \in U_2` such that the composition $`\phi_2 \circ f \circ \phi_1^{-1}` is holomorphic at $`\phi_1(p)`.
We say $`f` is a *morphism between Riemann surfaces* if and only if it is holomorphic at all points of $`X`.
:::

In other words: $`f` is holomorphic if and only if it is holomorphic as function mapping between local coordinates.

:::EXAMPLE
Some examples follows.

- The function $`f \colon \mathbb{C} \to \mathbb{C}` by $`f(x) = x^3` is a morphism.

  Note that this function is not bijective.
  At each point $`p \neq 0`, there is an open neighborhood on which $`f` has an inverse, but $`f` has no inverse at $`0`.
- The embedding of the complex plane into the Riemann sphere, $`\mathbb{C} \hookrightarrow \mathbb{C}_\infty`, is a morphism.
:::

# Functions to the Riemann sphere

:::PROTOTYPE
The meromorphic function $`\frac{1}{z}` can be made into a holomorphic $`\mathbb{C} \to \mathbb{C}_\infty` function.
:::

In this section, we will see that the Riemann sphere $`\mathbb{C}_\infty` can be viewed as "$`\mathbb{C}` with a point at infinity added".
This interpretation allows us to interpret meromorphic functions $`f \colon X \to \mathbb{C}` as holomorphic maps $`g \colon X \to \mathbb{C}_\infty`, which allows a much better handling of meromorphic functions — there's no longer any singularity, the resulting function $`g` is holomorphic everywhere.

First, $`\mathbb{C}_\infty` can be naturally interpreted as $`\mathbb{C}` with a single point added: identify $`\mathbb{C}_\infty \setminus \{N\}` with $`E_1` (and thus with $`\mathbb{C}`) through the chart $`\phi_1`, and let $`\infty` be the point $`N`.

:::QUESTION
Convince yourself that it makes sense to call this point $`\infty`: for every sequence of points $`\{z_i\}` on $`\mathbb{C}` such that $`|z_i| \to +\infty`, then $`\phi_1^{-1}(z_i) \to \infty` on $`\mathbb{C}_\infty` as a topological space.
:::

So, let $`X` be a Riemann surface, and $`f \colon X \to \mathbb{C}` be a meromorphic function on $`X`.
Naturally, $`g` can be defined by
$$`g(z) = \begin{cases} f(z) & \text{if } f(z) \neq \infty \\ \infty & \text{if } f(z) = \infty. \end{cases}`
Then $`g` is continuous — but furthermore, it's analytic.

:::QUESTION
At points $`z \in X` where $`g(z) \neq \infty`, $`g` is clearly analytic.
Convince yourself that $`g` is also analytic at $`z \in X` where $`g(z) = \infty`.
(Take a small open set $`U \subseteq X` around such a $`z` and re-parametrize $`g(U) \subseteq \mathbb{C}_\infty` by $`t = 1/z`.)
:::

Therefore:

:::PROPOSITION "Meromorphic-to-Riemann-sphere correspondence"
There is a one-to-one correspondence between meromorphic functions $`f \colon X \to \mathbb{C}` and holomorphic maps $`g \colon X \to \mathbb{C}_\infty` such that $`g` is not identically $`\infty`.
:::

Or, more informally:

:::MORAL
Plugging in the hole at $`\infty` of $`\mathbb{C}` allows us to analytically extend meromorphic functions to $`\mathbb{C} \cup \{\infty\}`-maps which are holomorphic everywhere.
:::

# Some other nice properties

We have just seen in the last section that the Riemann sphere $`\mathbb{C}_\infty` allows us to remove the singularities of meromorphic functions.
Informally speaking, this is because $`\mathbb{C}_\infty` is a "compactification" of $`\mathbb{C}` — adding a point to make it compact — and compact Riemann surfaces enjoy many nice properties.

:::PROPOSITION "Fiber count is constant"
Let $`X` and $`Y` be compact Riemann surfaces and $`f \colon X \to Y` be holomorphic and not constant.
For each point $`y \in Y`, define $`d_y` to be the total multiplicity of the points in the preimage of $`y`.
Then $`d_y` is well-defined and constant.
:::

You can see why this proposition is surprising:

::::EXAMPLE "The proposition does not hold for smooth compact manifolds"
Consider the following function $`f \colon X \to Y` between compact smooth real $`1`-manifold, depicted as a plot with $`x` and $`y`-axis.
(Note that a compact $`1`-manifold cannot be embedded into $`\mathbb{R}`, because compact subsets of $`\mathbb{R}` are closed and bounded, thus necessarily have a boundary.
A proper graph would live in a $`4`-dimensional space, which is rather difficult to visualize, so we settle with an approximate representation.)

:::figure "figures/riemann-surfaces/morphism-counterexample.svg"
:::

Here, $`X` and $`Y` are both isomorphic to the unit circle.

We count the number of points in the fiber above each point in $`Y`:

- Above point $`A`, there are infinitely many points.
- Above point $`B`, there is only one point. (You can argue that this point has "multiplicity $`2`" however)
- Above point $`C`, there are two points.
- Above point $`D`, the fiber is empty.
::::

:::DEFINITION "Degree of a map"
The value $`d_y` above is called the *degree* of the map $`f`, written $`\deg(f)`.
:::

:::EXAMPLE "Degree of the power map"
The map $`z \mapsto z^k`, when extended to a $`\mathbb{C}_\infty \to \mathbb{C}_\infty` map, has degree $`k`.
:::

If $`t \neq 0`, then $`t` has $`k` distinct $`k`-th roots.
But if $`t = 0`, its preimage consists only of the point $`0` — in this case, we wish to say $`z = 0` is a "multiple point".
We will formalize this next section when we define the multiplicity of a map.

This concept of degree coincides with the degree in homology when $`X` and $`Y` are both Riemann spheres — it counts how many spherical bags the image of $`f` consists of.
But, in this case, the theory is extra nice: not only is the graph homotopy equivalent to one that covers each point $`d` times, but each point is in fact covered *exactly* $`d` times.

This theme will be recurrent in complex analysis and Riemann surfaces:

:::MORAL
If the "things" are counted properly, the formula is very nice.
:::

The proof of the proposition is not difficult — the main observation is that the theorem is true for functions of the form $`f(z) = z^n`, and locally around each point $`p \in X`, $`f` is either an isomorphism or has the form above.
So $`d_y` is locally constant, and thus constant because $`Y` is connected.

# Multiplicity of a map

:::PROTOTYPE
$`f(x) = (x - 3)^2` has $`\mathrm{mult}_3(f) = 2`.
:::

In the previous section, we informally talked about the multiplicity of a map at a point.
We will rigorously define it in this section.

:::EXAMPLE "Fiber size jumps at branch points"
Consider the map $`f \colon \mathbb{C} \to \mathbb{C}` given by $`f(z) = z^5 + 1`.
Above each point $`y \in \mathbb{C}`, the fiber $`f^{-1}(y)` has $`5` points — except when $`y = 1`, where $`f^{-1}(1) = \{0\}` has only $`1` point.
:::

This behavior is *undesirable*, and we would like to say that the function $`f` maps $`5` "identical copies" of the point $`0` to the point $`1`.
(Equivalently: for each sequence $`\{y_i\}` converging to $`1`, there are $`5` different sequences $`\{x_i\}` converging to $`0` such that $`f(x_i) = y_i` for each $`i`.)

Inspired by this, we will define multiplicity in a way such that:

- $`z \mapsto z^m` has multiplicity $`m`, for integer $`m \geq 1`.
- If we perform an analytic reparametrization of the source or the target, then the degree does not change.

These two properties completely determine the degree.
We have the following:

:::PROPOSITION "Local normal form"
Let $`f \colon X \to Y` be a nonconstant holomorphic map defined at $`p \in X`.
Then there is a unique integer $`m \geq 1` such that, for every chart $`\phi_2 \colon U_2 \to V_2` on $`Y` centered at $`f(p)` (that is, $`\phi_2(f(p)) = 0`), there is a chart $`\phi_1 \colon U_1 \to V_1` on $`X` centered at $`p` such that the induced map $`\phi_2 \circ f \circ \phi_1^{-1} \colon V_1 \to V_2` has the form $`z \mapsto z^m`.
:::

In other words, once we fix a chart of $`Y`, there exists a chart of (an open subset of) $`X` such that the induced map between open subsets of $`\mathbb{C}` is a power map; furthermore, the exponent is independent of the selection.

:::MORAL
Every map looks locally like $`z \mapsto z^m`.
:::

::::PROOF
Essentially, use the Taylor expansion to determine $`m`, then the selection of $`\phi_1` is pretty much fixed by the restrictions.
::::

:::DEFINITION "Multiplicity"
The value $`m` above is the *multiplicity* of $`f` at point $`p`, written $`\mathrm{mult}_p(f)`.
:::

:::EXAMPLE "Multiplicities of various maps"
- The function $`z \mapsto z^{-2}`, extended to a $`\mathbb{C} \to \mathbb{C}_\infty` map, has multiplicity $`2` at the point $`0` — "two copies" of $`0` are mapped to $`\infty`.
- The function $`f(z) = (z - 1)(z - 2)^5` has $`\mathrm{mult}_2(f) = 5` — more generally, if $`p` is a root of $`f`, then $`\mathrm{mult}_p(f)` is the multiplicity of the root.
- The function $`z \mapsto z + 1` has multiplicity $`1` everywhere — in fact, the multiplicity of a nonconstant map at "most" points will be $`1`.
:::

These are the official terms:

:::DEFINITION "Ramification and branch points"
A point $`p` such that $`\mathrm{mult}_p(f) > 1` is called a *ramification point*.
In that case, the point $`f(p)` is called a *branch point*.
:::

# The sum of the orders of a meromorphic function

Yet another case where we get a nice formula.

:::EXAMPLE "Zero-pole counts on the Riemann sphere"
Consider some meromorphic $`\mathbb{C}_\infty \to \mathbb{C}_\infty` functions (defined by extending a $`\mathbb{C} \to \mathbb{C}` function the obvious way), and list the zeros and poles (with multiplicity):

| Function | Zeros | Poles |
| --- | --- | --- |
| $`5` | none | none |
| $`(x + 1)^2` | $`-1, -1` | $`\infty, \infty` |
| $`\frac{1}{x^2 + 1}` | $`\infty, \infty` | $`i, -i` |
| $`\frac{x + 1}{x + 2}` | $`-1` | $`-2` |

Every time, the number of zeros equals the number of poles.
:::

This is not a coincidence:

:::PROPOSITION "Sum of orders is zero"
Let $`f \colon X \to \mathbb{C}` be a nonconstant meromorphic function on a compact Riemann surface $`X`.
Then
$$`\sum_p \mathrm{ord}_p(f) = 0.`
:::

Of course, we need $`X` to be compact — there certainly are $`\mathbb{C} \to \mathbb{C}` functions that have several zeros but no poles.

::::PROOF
Extend $`f` to an $`X \to \mathbb{C}_\infty` function; then the sum of multiplicities of points in the fiber of $`0` equals that in the fiber of $`\infty`.
::::

# The Hurwitz formula

The Hurwitz formula relates the genera of $`X` and $`Y` and the ramification data of a non-constant holomorphic $`f \colon X \to Y` between compact Riemann surfaces; it says
$$`2 g_X - 2 = \deg(f) (2 g_Y - 2) + \sum_{p \in X} (\mathrm{mult}_p(f) - 1).`
A formal statement requires defining the genus first, which is a topological invariant we have not yet built up, so we leave the precise discussion to a later chapter.

# The identity theorem

The following propositions are expected — the same behavior is seen in complex analysis with holomorphic functions.

:::THEOREM "Identity theorem for Riemann surfaces"
Let $`f, g \colon X \to Y` be holomorphic maps between Riemann surfaces.
If $`f = g` on a nonempty open subset of $`X`, then $`f = g`.
:::

This is the analog of the identity theorem for ordinary holomorphic functions on a connected open subset of $`\mathbb{C}`.
Note that here the assumption that $`X` is connected is used — the disjoint union of two copies of $`\mathbb{C}` is a smooth $`2`-manifold, but not a Riemann surface.

That is:

:::MORAL
Holomorphic maps are *rigid* — the value of a function on a tiny subset determines its value everywhere.
:::

# Formalization

:::LEANCOMPANION
:::

## Definition

The "compose with charts on both sides" definition is exactly what `MDifferentiable I I' f` packages.
For Riemann surfaces both the source and the target carry the trivial complex model $`\mathcal{I}(\mathbb{C}, \mathbb{C})`, written `𝓘(ℂ, ℂ)`, so a morphism is the following.
The manifold-differentiability machinery then reduces, around each point, to ordinary holomorphy of $`\phi_2 \circ f \circ \phi_1^{-1}` on its open set of definition.

```lean
example (f : ℂ → ℂ) : Prop :=
  MDifferentiable (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f
```

Working inside a single chart, holomorphy at a point $`p` is `AnalyticAt ℂ f p`.
The example map $`z \mapsto z^3` is holomorphic at every point.

```lean
example (p : ℂ) : AnalyticAt ℂ (fun z : ℂ => z ^ 3) p := by
  apply AnalyticAt.pow
  exact analyticAt_id
```

A composition of holomorphic maps is holomorphic, which is what makes "holomorphic in charts" a well-behaved notion.

```lean
example (f g : ℂ → ℂ) (p : ℂ) (hf : AnalyticAt ℂ f (g p))
    (hg : AnalyticAt ℂ g p) : AnalyticAt ℂ (f ∘ g) p := by
  sorry
```

:::solution
```lean
example (f g : ℂ → ℂ) (p : ℂ) (hf : AnalyticAt ℂ f (g p))
    (hg : AnalyticAt ℂ g p) : AnalyticAt ℂ (f ∘ g) p :=
  hf.comp hg
```
:::

## Functions to the Riemann sphere

The "meromorphic" side is captured by `MeromorphicAt f x`: there exists a natural number $`n` such that $`(z - x)^n \cdot f(z)` is analytic at $`x`.

```lean
recall MeromorphicAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : 𝕜 → E) (x : 𝕜) : Prop
```

The "holomorphic-to-the-sphere" side is `MDifferentiable (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g` for a map $`g \colon X \to \mathrm{OnePoint}\;\mathbb{C}` into the one-point compactification, which is the spelling of the Riemann sphere $`\mathbb{C}_\infty`.
A packaged "extend a meromorphic function to a Riemann-sphere-valued map" lemma is not yet available; the order-of-pole machinery `meromorphicOrderAt`, met below, already records pole and zero multiplicities.

Every function holomorphic at a point is in particular meromorphic there.

```lean
example (f : ℂ → ℂ) (x : ℂ) (h : AnalyticAt ℂ f x) :
    MeromorphicAt f x := h.meromorphicAt
```

The prototypical meromorphic function $`\frac{1}{z}` is meromorphic at its pole $`0`.

```lean
example : MeromorphicAt (fun z : ℂ => z⁻¹) 0 := by
  apply MeromorphicAt.inv
  exact analyticAt_id.meromorphicAt
```

Show the same for a pole placed at an arbitrary point $`x`.

```lean
example (x : ℂ) : MeromorphicAt (fun z : ℂ => (z - x)⁻¹) x := by
  sorry
```

:::solution
```lean
example (x : ℂ) : MeromorphicAt (fun z : ℂ => (z - x)⁻¹) x := by
  apply MeromorphicAt.inv
  exact (analyticAt_id.sub analyticAt_const).meromorphicAt
```
:::

## Some other nice properties

The global degree of a nonconstant holomorphic map between compact Riemann surfaces — the constant fibre count $`d_y` — is not part of Mathlib, since it presupposes the compact surfaces themselves as objects that are not yet packaged.
What *is* available is the local engine behind "the fibre count is locally constant": the open mapping theorem `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`.
Around each point a holomorphic map is either locally constant or locally open, and openness is what forces nearby fibres to have the same size.

```lean
example (g : ℂ → ℂ) (z₀ : ℂ) (hg : AnalyticAt ℂ g z₀) :
    (∀ᶠ z in 𝓝 z₀, g z = g z₀) ∨
      𝓝 (g z₀) ≤ Filter.map g (𝓝 z₀) :=
  hg.eventually_constant_or_nhds_le_map_nhds
```

## Multiplicity of a map

The multiplicity $`\mathrm{mult}_p(f)` is `analyticOrderAt f x : ℕ∞`: for a function analytic at $`x` and not identically zero nearby, it returns the unique $`n` with $`f(z)/(z - x)^n` analytic and nonzero at $`x`.
Read in charts this is exactly the local exponent $`m` in the normal form $`z \mapsto z^m`; `AnalyticAt.analyticOrderAt_eq_natCast` and the surrounding order API codify the "looks locally like $`z^m`" picture.

The power map $`z \mapsto z^n` has multiplicity $`n` at the origin, matching $`\mathrm{mult}_0(z^n) = n`.

```lean
example (n : ℕ) : analyticOrderAt (fun z : ℂ => z ^ n) 0 = n := by
  have h : (fun z : ℂ => z ^ n) = (fun x : ℂ => x - 0) ^ n := by
    funext z; simp
  rw [h]
  exact analyticOrderAt_centeredMonomial
```

A point where the value is nonzero is not a zero at all, so its order is $`0`.

```lean
example (f : ℂ → ℂ) (x : ℂ) (hf : AnalyticAt ℂ f x)
    (h : f x ≠ 0) : analyticOrderAt f x = 0 := by
  sorry
```

:::solution
```lean
example (f : ℂ → ℂ) (x : ℂ) (hf : AnalyticAt ℂ f x)
    (h : f x ≠ 0) : analyticOrderAt f x = 0 :=
  hf.analyticOrderAt_eq_zero.mpr h
```
:::

The bare order `analyticOrderAt f x` measures how fast `f` *vanishes* at `x`, so it reads the multiplicity only when $`f(p) = 0`.
The genuine local multiplicity $`\mathrm{mult}_p(f)` recenters on the value, taking the order of $`z \mapsto f(z) - f(p)`; this recentered packaging is `ramificationIndex f p`, recorded in `Napkin.Missing.RamifiedMap` since Mathlib has the order but not the "ramification index of a surface map" wrapper.

The power map $`z \mapsto z^5` ramifies to order $`5` at the origin, so its ramification index there is $`5`.

```lean
example : ramificationIndex (fun z : ℂ => z ^ 5) 0 = 5 :=
  ramificationIndex_centeredMonomial 5 (by norm_num)
```

Because $`z \mapsto f(z) - f(p)` vanishes at $`p` by construction, the ramification index of a map analytic there is always at least $`1` — a nonconstant map never has multiplicity $`0`.

```lean
example (f : ℂ → ℂ) (p : ℂ)
    (hf : AnalyticAt ℂ (fun z => f z - f p) p) :
    ramificationIndex f p ≠ 0 :=
  ramificationIndex_ne_zero f p hf
```

Show that the cube map $`z \mapsto z^3` has ramification index $`3` at the origin, its unique ramification point.

```lean
example : ramificationIndex (fun z : ℂ => z ^ 3) 0 = 3 := by
  sorry
```

:::solution
```lean
example : ramificationIndex (fun z : ℂ => z ^ 3) 0 = 3 :=
  ramificationIndex_centeredMonomial 3 (by norm_num)
```
:::

## The sum of the orders of a meromorphic function

The global statement $`\sum_p \mathrm{ord}_p(f) = 0` on a compact Riemann surface is not in Mathlib, again because the compact surface is not an available object.
The per-point order that the sum ranges over *is* available as `meromorphicOrderAt f x : WithTop ℤ`, valued in the integers-with-infinity so that a pole records a negative order.
For instance $`\frac{1}{z}` has order $`-1` at its pole.

```lean
example : meromorphicOrderAt (fun z : ℂ => z⁻¹) 0 = (-1 : ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff (by fun_prop)]
  refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
  filter_upwards with z
  simp [zpow_neg, zpow_one, smul_eq_mul]
```

Conversely, a function analytic and nonvanishing at $`x` contributes order $`0` to such a sum.

```lean
example (f : ℂ → ℂ) (x : ℂ) (hf : AnalyticAt ℂ f x)
    (h : f x ≠ 0) : meromorphicOrderAt f x = 0 := by
  sorry
```

:::solution
```lean
example (f : ℂ → ℂ) (x : ℂ) (hf : AnalyticAt ℂ f x)
    (h : f x ≠ 0) : meromorphicOrderAt f x = 0 := by
  rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_zero.mpr h]
  rfl
```
:::

## The Hurwitz formula

The Hurwitz formula couples the genera of $`X` and $`Y` with the ramification data of the map, and the genus is a topological invariant that Mathlib does not yet attach to these surfaces.
Following the pattern used for Riemann–Roch, the identity is bundled as a statement-as-structure `RiemannHurwitzData` in `Napkin.Missing.RamifiedMap`: it carries the source and target genera $`g_X, g_Y`, the degree $`d`, the finite set of ramification points with their multiplicities `e p`, and the Hurwitz identity
$$`2 g_X - 2 = d (2 g_Y - 2) + \sum_p (\mathrm{mult}_p(f) - 1)`
itself as a field.
The multiplicities `e p` are the ramification indices of the previous section; the genus and degree stay abstract, so the structure records exactly the data Mathlib cannot yet build, and its consequences become derivable.

Solving the identity for the source genus puts it in the form one reads a computed genus off of.

```lean
example {X : Type} (H : RiemannHurwitzData X) :
    2 * (H.gX : ℤ)
      = H.d * (2 * H.gY - 2) + H.totalRamification + 2 :=
  H.two_gX_eq
```

The hyperelliptic case is a degree-$`2` cover of the sphere ($`d = 2`, $`g_Y = 0`) with $`2g + 2` branch points, each of multiplicity $`2`, so the total ramification $`\sum_p (\mathrm{mult}_p(f) - 1) = 2g + 2`.
The formula then forces the source genus to be exactly $`g`, since $`2 g_X - 2 = 2(-2) + (2g + 2) = 2g - 2`.

```lean
example {X : Type} (H : RiemannHurwitzData X) (g : ℕ)
    (hd : H.d = 2) (hY : H.gY = 0)
    (hR : H.totalRamification = 2 * g + 2) : H.gX = g :=
  H.genus_of_double_cover hd hY g hR
```

As a reader exercise, derive the Hurwitz monotonicity bound: a nonconstant map ($`d \geq 1`) onto a target of positive genus ($`g_Y \geq 1`) can only raise the genus, $`g_Y \leq g_X`, because $`2 g_Y - 2 \geq 0` makes the degree factor and the nonnegative ramification term only add.

```lean
example {X : Type} (H : RiemannHurwitzData X)
    (hpos : 0 ≤ H.totalRamification) (hd : 1 ≤ H.d)
    (hY : 1 ≤ H.gY) : (H.gY : ℤ) ≤ H.gX := by
  sorry
```

:::solution
```lean
example {X : Type} (H : RiemannHurwitzData X)
    (hpos : 0 ≤ H.totalRamification) (hd : 1 ≤ H.d)
    (hY : 1 ≤ H.gY) : (H.gY : ℤ) ≤ H.gX :=
  H.hurwitz_bound hpos hd hY
```
:::

## The identity theorem

The one-chart counterpart is `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`: if two functions are analytic on a preconnected open set $`U` and agree on a neighborhood of some point $`x \in U`, they agree on all of $`U`.
The Riemann-surface version is the patched-together statement obtained by transporting this fact across charts using the connectedness of $`X`.

```lean
example {f g : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) {z₀ : ℂ}
    (h₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) : Set.EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU h₀ hfg
```

On all of $`\mathbb{C}`, which is connected, this specializes to rigidity: two entire functions that agree near a point agree everywhere.

```lean
example {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) {z₀ : ℂ}
    (hfg : f =ᶠ[𝓝 z₀] g) : f = g := by
  sorry
```

:::solution
```lean
example {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) {z₀ : ℂ}
    (hfg : f =ᶠ[𝓝 z₀] g) : f = g := by
  have h := hf.eqOn_of_preconnected_of_eventuallyEq hg
    isPreconnected_univ (Set.mem_univ z₀) hfg
  funext z
  exact h (Set.mem_univ z)
```
:::
