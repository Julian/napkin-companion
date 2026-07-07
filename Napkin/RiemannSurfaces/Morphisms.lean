import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Geometry.Manifold.Complex

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

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

In other words: $`f` is holomorphic if and only if it is holomorphic as a function mapping between local coordinates.

This "compose with charts on both sides" definition is exactly what `MDifferentiable I I' f` packages on the Mathlib side.
For Riemann surfaces, both source and target carry the trivial complex model, so the relevant typeclass is `MDifferentiable (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f`; the manifold-differentiability machinery then automatically reduces, around each point, to ordinary holomorphy of $`\phi_2 \circ f \circ \phi_1^{-1}` on its open set of definition.

:::EXAMPLE "Some morphisms"
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

In Mathlib, the "meromorphic" side is captured by `MeromorphicAt f x` (resp. `MeromorphicOn f s`) — defined as: there exists a natural number $`n` such that $`(z - x)^n \cdot f(z)` is analytic at $`x`.
The "holomorphic-to-the-sphere" side is `MDifferentiable (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g` for $`g \colon X \to \mathrm{OnePoint}\;\mathbb{C}` (the one-point compactification, which is Mathlib's spelling of the Riemann sphere).
A formal "extend a meromorphic function to a Riemann-sphere-valued map" lemma is on the active wishlist; the order-of-pole machinery `MeromorphicAt.order` already lets you talk about pole/zero multiplicities.

```lean
recall MeromorphicAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : 𝕜 → E) (x : 𝕜) : Prop
```

# Some other nice properties

We have just seen in the last section that the Riemann sphere $`\mathbb{C}_\infty` allows us to remove the singularities of meromorphic functions.
Informally speaking, this is because $`\mathbb{C}_\infty` is a "compactification" of $`\mathbb{C}` — adding a point to make it compact — and compact Riemann surfaces enjoy many nice properties.

:::PROPOSITION "Fiber count is constant"
Let $`X` and $`Y` be compact Riemann surfaces and $`f \colon X \to Y` be holomorphic and not constant.
For each point $`y \in Y`, define $`d_y` to be the total multiplicity of the points in the preimage of $`y`.
Then $`d_y` is well-defined and constant.
:::

You can see why this proposition is surprising:

:::EXAMPLE "Smooth-manifold counterexample"
The proposition does not hold for smooth compact manifolds.
Consider a smooth $`f \colon X \to Y` between two compact smooth real $`1`-manifolds, both isomorphic to the unit circle, where the graph of $`f` over $`Y` looks like an irregular wave: there are points $`y \in Y` whose fiber is empty, points whose fiber is a single point, points whose fiber has two points, and a region where the fiber is infinite.

(Note that a compact $`1`-manifold cannot be embedded into $`\mathbb{R}`, because compact subsets of $`\mathbb{R}` are closed and bounded, thus necessarily have a boundary.
A proper graph would live in a $`4`-dimensional space, which is rather difficult to visualize.)
:::

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

The Mathlib analog is `AnalyticAt.order` (and `MeromorphicAt.order`): given an analytic function $`f` at $`x` that is not identically zero in a neighborhood, `AnalyticAt.order hf : ℕ∞` returns the order of the zero (the unique $`n` such that $`f(z)/(z-x)^n` is analytic and nonzero at $`x`), which is exactly the multiplicity above when working on $`\mathbb{C}` charts.
Mathlib's `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` and the order API codify the "looks locally like $`z^m`" intuition.

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

The Mathlib counterpart on a single chart is `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` in `Mathlib.Analysis.Analytic.IsolatedZeros`: if two functions are analytic on a preconnected open set $`U` and agree on a neighborhood of some point $`x \in U`, they agree on all of $`U`.
The Riemann-surface version is the patched-together statement obtained by transporting this fact across charts using the connectedness of $`X`.

That is:

:::MORAL
Holomorphic maps are *rigid* — the value of a function on a tiny subset determines its value everywhere.
:::
