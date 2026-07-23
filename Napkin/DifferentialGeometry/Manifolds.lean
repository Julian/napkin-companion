import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.RingTheory.Ideal.Cotangent
import Napkin.Missing.ManifoldForm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing

set_option pp.rawOnError true

#doc (Manual) "A bit of manifolds" =>

%%%
file := "Manifolds"
%%%

Last chapter, we stated Stokes' theorem for cells.
It turns out there is a much larger class of spaces, the so-called *smooth manifolds*, for which this makes sense.

Unfortunately, the definition of a smooth manifold is *complete garbage*, and so by the time I am done defining differential forms and orientations, I will be too lazy to actually define what the integral on it is, and just wave my hands and state Stokes' theorem.

# Topological manifolds

:::PROTOTYPE
$`S^2`: "the Earth looks flat".
:::

Long ago, people thought the Earth was flat, i.e. homeomorphic to a plane, and in particular they thought that $`\pi_2(\text{Earth}) = 0`.
But in fact, as most of us know, the Earth is actually a sphere, which is not contractible and in particular $`\pi_2(\text{Earth}) \cong \mathbb{Z}`.
This observation underlies the definition of a manifold:

:::MORAL
An $`n`-manifold is a space which locally looks like $`\mathbb{R}^n`.
:::

Actually there are two ways to think about a topological manifold $`M`:

- *Locally*: at every point $`p \in M`, some open neighborhood of $`p` looks like an open set of $`\mathbb{R}^n`.
  For example, to someone standing on the surface of the Earth, the Earth looks much like $`\mathbb{R}^2`.
- *Globally*: there exists an open cover of $`M` by open sets $`\{U_i\}_i` (possibly infinite) such that each $`U_i` is homeomorphic to some open subset of $`\mathbb{R}^n`.
  For example, from outer space, the Earth can be covered by two hemispherical pancakes.

:::QUESTION
Check that these are equivalent.
:::

While the first is the best motivation for examples, the second is easier to use formally.

:::DEFINITION
A *topological $`n`-manifold* $`M` is a Hausdorff space with an open cover $`\{U_i\}` of sets homeomorphic to subsets of $`\mathbb{R}^n`, say by homeomorphisms
$$`\phi_i \colon U_i \xrightarrow{\cong} E_i \subseteq \mathbb{R}^n`
where each $`E_i` is an open subset of $`\mathbb{R}^n`.
Each $`\phi_i \colon U_i \to E_i` is called a *chart*, and together they form a so-called *atlas*.
:::

:::REMARK
Here "$`E`" stands for "Euclidean".
I think this notation is not standard; usually people just write $`\phi_i(U_i)` instead.
:::

:::REMARK
This definition is nice because it doesn't depend on embeddings: a manifold is an *intrinsic* space $`M`, rather than a subset of $`\mathbb{R}^N` for some $`N`.
Analogy: an abstract group $`G` is an intrinsic object rather than a subgroup of $`S_n`.
:::

::::EXAMPLE "An atlas on the circle"
Take $`M = S^1`.
Two open arcs covering the circle, each missing one antipodal point and each homeomorphic to an open interval in $`\mathbb{R}`, give an atlas with two charts.

:::figure "figures/differential-geometry/manifolds-s1-charts.svg"
Two chart arcs $`U_1`, $`U_2` cover $`S^1`, each mapped to an interval by a chart $`\phi_i`.
:::
::::

:::QUESTION
Where do you think the words "chart" and "atlas" come from?
:::

:::EXAMPLE "Some topological manifolds"
- The sphere $`S^2` is a $`2`-manifold: every point in the sphere has a small open neighborhood that looks like $`D^2`.
  One can cover the Earth with just two hemispheres, and each hemisphere is homeomorphic to a disk.
- The circle $`S^1` is a $`1`-manifold; every point has an open neighborhood that looks like an open interval.
- The torus, Klein bottle, and $`\mathbb{RP}^2` are all $`2`-manifolds.
- $`\mathbb{R}^n` is trivially a manifold, as are its open sets.

All these spaces are compact except $`\mathbb{R}^n`.

A non-example is the closed disk $`D^n`, because it has a *boundary*; points on the boundary do not have open neighborhoods that look Euclidean.
:::

# Smooth manifolds

:::PROTOTYPE
All the topological manifolds.
:::

Let $`M` be a topological $`n`-manifold with atlas $`\{U_i \xrightarrow{\phi_i} E_i\}`.

:::DEFINITION
For any $`i, j` such that $`U_i \cap U_j \neq \varnothing`, the *transition map* $`\phi_{ij}` is the composed map
$$`\phi_{ij} \colon E_i \cap \phi_i(U_i \cap U_j) \xrightarrow{\phi_i^{-1}} U_i \cap U_j \xrightarrow{\phi_j} E_j \cap \phi_j(U_i \cap U_j).`
:::

Sorry for the dense notation, let me explain.
The intersection with the image $`\phi_i(U_i \cap U_j)` and the image $`\phi_j(U_i \cap U_j)` is a notational annoyance to make the map well-defined and a homeomorphism.
The transition map is just the natural way to go from $`E_i \to E_j`, restricted to overlaps.

:::figure "figures/differential-geometry/manifolds-s1-transition.svg"
On the overlap $`U_1 \cap U_2`, the transition map $`\phi_{12}` passes between the two charts.
:::

We want to add enough structure so that we can use differential forms.

:::DEFINITION
We say $`M` is a *smooth manifold* if all its transition maps are smooth.
:::

This definition makes sense because we know what it means for a map between two open sets of $`\mathbb{R}^n` to be differentiable.

With smooth manifolds we can try to port over definitions that we built for $`\mathbb{R}^n` onto our manifolds.
So in general, all definitions involving smooth manifolds will reduce to something on each of the coordinate charts, with a compatibility condition.

As an example, here is the definition of a "smooth map":

:::DEFINITION
- Let $`M` be a smooth manifold.
  A continuous function $`f \colon M \to \mathbb{R}` is called *smooth* if the composition
  $$`E_i \xrightarrow{\phi_i^{-1}} U_i \hookrightarrow M \xrightarrow{f} \mathbb{R}`
  is smooth as a function $`E_i \to \mathbb{R}` for each $`i`.
- Let $`M` and $`N` be smooth, with atlases $`\{U_i^M \xrightarrow{\phi_i} E_i^M\}_i` and $`\{U_j^N \xrightarrow{\phi_j} E_j^N\}_j`.
  A map $`f \colon M \to N` is *smooth* if for every $`i` and $`j`, the composed map
  $$`E_i \xrightarrow{\phi_i^{-1}} U_i \hookrightarrow M \xrightarrow{f} N \twoheadrightarrow U_j \xrightarrow{\phi_j} E_j`
  is smooth, as a function $`E_i \to E_j`.
:::

# Regular value theorem

:::PROTOTYPE
$`x^2 + y^2 = 1` is a circle!
:::

Despite all that I've written about general manifolds, it would be sort of mean if I left you here because I have not really told you how to actually construct manifolds in practice, even though we know the circle $`x^2 + y^2 = 1` is a great example of a one-dimensional manifold embedded in $`\mathbb{R}^2`.

:::THEOREM "Regular value theorem"
Let $`V` be an $`n`-dimensional real normed vector space, let $`U \subseteq V` be open, and let $`f_1, \dots, f_m \colon U \to \mathbb{R}` be smooth functions.
Let $`M` be the set of points $`p \in U` such that $`f_1(p) = \dots = f_m(p) = 0`.

Assume $`M` is nonempty and that the map
$$`V \to \mathbb{R}^m \quad \text{by} \quad v \mapsto \left( (Df_1)_p(v), \dots, (Df_m)_p(v) \right)`
has rank $`m`, for every point $`p \in M`.
Then $`M` is a manifold of dimension $`n - m`.
:::

For a proof, see {cite}`ref:manifolds`, Theorem 6.3.

One very common special case is to take $`m = 1` above.

:::THEOREM "Level hypersurfaces"
Let $`V` be a finite-dimensional real normed vector space, let $`U \subseteq V` be open, and let $`f \colon U \to \mathbb{R}` be smooth.
Let $`M` be the set of points $`p \in U` such that $`f(p) = 0`.
If $`M \neq \varnothing` and $`(Df)_p` is not the zero map for any $`p \in M`, then $`M` is a manifold of dimension $`\dim V - 1`.
:::

:::EXAMPLE "The circle x²+y²-c=0"
Let $`f(x, y) = x^2 + y^2 - c`, $`f \colon \mathbb{R}^2 \to \mathbb{R}`, where $`c` is a positive real number.
Note that
$$`Df = 2x \cdot dx + 2y \cdot dy`
which in particular is nonzero as long as $`(x, y) \neq (0, 0)`, i.e. as long as $`c \neq 0`.
Thus:

- When $`c > 0`, the resulting curve — a circle with radius $`\sqrt{c}` — is a one-dimensional manifold, as we knew.
- When $`c = 0`, the result fails.
  Indeed, $`M` is a single point, which is actually a zero-dimensional manifold.
:::

We won't give further examples since I'm only mentioning this in passing in order to increase your capacity to write real concrete examples.
(But {cite}`ref:manifolds`, Chapter 6.2 has some more examples, beautifully illustrated.)

# Differential forms on manifolds

We already know what a differential form is on an open set $`U \subseteq \mathbb{R}^n`.
So, we naturally try to port over the definition of differential form on each subset, plus a compatibility condition.

Let $`M` be a smooth manifold with atlas $`\{U_i \xrightarrow{\phi_i} E_i\}_i`.

:::DEFINITION
A *differential $`k`-form* $`\alpha` on a smooth manifold $`M` is a collection $`\{\alpha_i\}_i` of differential $`k`-forms on each $`E_i`, such that for any $`j` and $`i` we have
$$`\alpha_j = \phi_{ij}^\ast (\alpha_i).`
:::

In English: we specify a differential form on each chart, which is compatible under pullbacks of the transition maps.

# Orientations

:::PROTOTYPE
Left versus right, clockwise vs. counterclockwise.
:::

This still isn't enough to integrate on manifolds.
We need one more definition: that of an orientation.

The main issue is the observation from standard calculus that
$$`\int_a^b f(x) \; dx = -\int_b^a f(x) \; dx.`
Consider then a space $`M` which is homeomorphic to an interval.
If we have a $`1`-form $`\alpha`, how do we integrate it over $`M`?
Since $`M` is just a topological space (rather than a subset of $`\mathbb{R}`), there is no default "left" or "right" that we can pick.
As another example, if $`M = S^1` is a circle, there is no default "clockwise" or "counterclockwise" unless we decide to embed $`M` into $`\mathbb{R}^2`.

To work around this, we have to make additional assumptions about our manifold.

:::DEFINITION
A smooth $`n`-manifold is *orientable* if there exists a differential $`n`-form $`\omega` on $`M` such that for every $`p \in M`,
$$`\omega_p \neq 0.`
:::

Recall here that $`\omega_p` is an element of $`\bigwedge^n(V^\vee)`.
In that case we say $`\omega` is a *volume form* of $`M`.

How do we picture this definition?
A differential form is supposed to take tangent vectors of $`M` and return real numbers.
To this end, we can think of each point $`p \in M` as having a *tangent plane* $`T_p(M)` which is $`n`-dimensional.
Now since the volume form $`\omega` is $`n`-dimensional, it takes an entire basis of $`T_p(M)` and gives a real number.
So a manifold is orientable if there exists a consistent choice of sign for the basis of tangent vectors at every point of the manifold.

For "embedded manifolds", this just amounts to being able to pick a nonzero field of normal vectors to each point $`p \in M`.
For example, $`S^1` is orientable in this way; similarly, one can orient a sphere $`S^2` by having a field of vectors pointing away from (or toward) the center.

This is all non-rigorous, because I haven't defined the tangent plane $`T_p(M)`; since $`M` is in general an intrinsic object one has to be quite roundabout to define $`T_p(M)` (although I do so in an optional section later).
In any event, the point is that guesses about the orientability of spaces are likely to be correct.

:::EXAMPLE "Orientable surfaces"
- Spheres $`S^n`, planes, and the torus $`S^1 \times S^1` are orientable.
- The Möbius strip and Klein bottle are *not* orientable: they are "one-sided".
- $`\mathbb{CP}^n` is orientable for any $`n`.
- $`\mathbb{RP}^n` is orientable only for odd $`n`.
:::

# Stokes' theorem for manifolds

Stokes' theorem in the general case is based on the idea of a *manifold with boundary* $`M`, which I won't define, other than to say its boundary $`\partial M` is an $`(n - 1)`-dimensional manifold and that it is oriented if $`M` is oriented.
An example is $`M = D^2`, which has boundary $`\partial M = S^1`.

Next:

:::DEFINITION
The *support* of a differential form $`\alpha` on $`M` is the closure of the set
$$`\left\{ p \in M \mid \alpha_p \neq 0 \right\}.`
If this support is compact as a topological space, we say $`\alpha` is *compactly supported*.
:::

:::REMARK
For example, volume forms are supported on all of $`M`.
:::

Now, one can define integration on oriented manifolds, but I won't define this because the definition is truly awful.
Then Stokes' theorem says:

:::THEOREM "Stokes' theorem for manifolds"
Let $`M` be a smooth oriented $`n`-manifold with boundary and let $`\alpha` be a compactly supported $`(n-1)`-form.
Then
$$`\int_M d\alpha = \int_{\partial M} \alpha.`
:::

All the omitted details are developed in full in {cite}`ref:manifolds`.

# (Optional) The tangent and cotangent space

:::PROTOTYPE
Draw a line tangent to a circle, or a plane tangent to a sphere.
:::

Let $`M` be a smooth manifold and $`p \in M` a point.
I omitted the definition of $`T_p(M)` earlier, but want to actually define it now.

As I said, geometrically we know what this *should* look like for our usual examples.
For example, if $`M = S^1` is a circle embedded in $`\mathbb{R}^2`, then the tangent vector at a point $`p` should just look like a vector running off tangent to the circle.
Similarly, given a sphere $`M = S^2`, the tangent space at a point $`p` along the sphere would look like a plane tangent to $`M` at $`p`.

However, one of the points of all this manifold stuff is that we really want to see the manifold as an *intrinsic object*, in its own right, rather than as embedded in $`\mathbb{R}^n`.{margin}[This can be thought of as analogous to the way that we think of a group as an abstract object in its own right, even though Cayley's Theorem tells us that any group is a subgroup of the permutation group. Note this wasn't always the case! During the 19th century, a group was literally defined as a subset of $`\operatorname{GL}(n)` or of $`S_n`. In fact Sylow developed his theorems without the word "group". Only much later was the abstract definition of a group given, an abstract set $`G` which was independent of any *embedding* into $`S_n`, and an object in its own right.]
So we would like our notion of a tangent vector to not refer to an ambient space, but only to intrinsic properties of the manifold $`M` in question.

## Tangent space

To motivate this construction, let us start with an embedded case for which we know the answer already: a sphere.

:::figure "figures/differential-geometry/manifolds-s1-vector-field.svg"
A field of tangent vectors along the circle $`S^1`.
:::

Suppose $`f \colon S^2 \to \mathbb{R}` is a function on a sphere, and take a point $`p`.
Near the point $`p`, $`f` looks like a function on some open neighborhood of the origin.
Thus we can think of taking a *directional derivative* along a vector $`\vec{v}` in the imagined tangent plane (i.e. some partial derivative).
For a fixed $`\vec{v}` this partial derivative is a linear map
$$`D_{\vec{v}} \colon C^\infty(M) \to \mathbb{R}.`

It turns out this goes the other way: if you know what $`D_{\vec{v}}` does to every smooth function, then you can recover $`v`.
This is the trick we use in order to create the tangent space.
Rather than trying to specify a vector $`\vec{v}` directly (which we can't do because we don't have an ambient space):

:::MORAL
The vectors *are* partial-derivative-like maps.
:::

More formally, we have the following.

:::DEFINITION
A *derivation* $`D` at $`p` is a linear map $`D \colon C^\infty(M) \to \mathbb{R}` (i.e. assigning a real number to every smooth $`f`) satisfying the following Leibniz rule: for any $`f, g` we have the equality
$$`D(fg) = f(p) \cdot D(g) + g(p) \cdot D(f) \in \mathbb{R}.`
:::

This is just a "product rule".
Then the tangent space is easy to define:

:::DEFINITION
A *tangent vector* is just a derivation at $`p`, and the *tangent space* $`T_p(M)` is simply the set of all these tangent vectors.
:::

In this way we have constructed the tangent space.

:::figure "figures/differential-geometry/manifolds-tangent-space.svg"
The tangent space $`T_p(M)` at a point $`p` of $`S^1`, with a tangent vector $`\vec v`.
:::

## The cotangent space

In fact, one can show that the product rule for $`D` is equivalent to the following three conditions:

1. $`D` is linear, meaning $`D(af + bg) = a D(f) + b D(g)`.
2. $`D(1_M) = 0`, where $`1_M` is the constant function on $`M`.
3. $`D(fg) = 0` whenever $`f(p) = g(p) = 0`.
   Intuitively, this means that if a function $`h = fg` vanishes to second order at $`p`, then its derivative along $`D` should be zero.

This suggests a third equivalent definition: suppose we define
$$`\mathfrak{m}_p \overset{\text{def}}{=} \left\{ f \in C^\infty M \mid f(p) = 0 \right\}`
to be the set of functions which vanish at $`p` (this is called the *maximal ideal* at $`p`).
In that case,
$$`\mathfrak{m}_p^2 = \left\{ \sum_i f_i \cdot g_i \mid f_i(p) = g_i(p) = 0 \right\}`
is the set of functions vanishing to second order at $`p`.
Thus, a tangent vector is really just a linear map
$$`\mathfrak{m}_p / \mathfrak{m}_p^2 \to \mathbb{R}.`

In other words, the tangent space is actually the dual space of $`\mathfrak{m}_p / \mathfrak{m}_p^2`; for this reason, the space $`\mathfrak{m}_p / \mathfrak{m}_p^2` is defined as the *cotangent space* (the dual of the tangent space).

This definition is even more abstract than the one with derivations above, but has some nice properties:

- it is coordinate-free, and
- it's defined only in terms of the smooth functions $`M \to \mathbb{R}`, which will be really helpful later on in algebraic geometry when we have varieties or schemes and can repeat this definition.

## Sanity check

With all these equivalent definitions, the last thing I should do is check that this definition of tangent space actually gives a vector space of dimension $`n`.
To do this it suffices to show this for open subsets of $`\mathbb{R}^n`, which will imply the result for general manifolds $`M` (which are locally open subsets of $`\mathbb{R}^n`).
Using some real analysis, one can prove the following result:

:::THEOREM "Maximal ideal at the origin"
Suppose $`M \subset \mathbb{R}^n` is open and $`0 \in M`.
Then
$$`\mathfrak{m}_0 = \{ \text{smooth functions } f \mid f(0) = 0 \}`
$$`\mathfrak{m}_0^2 = \{ \text{smooth functions } f \mid f(0) = 0, (\nabla f)_0 = 0 \}.`
In other words $`\mathfrak{m}_0^2` is the set of functions which vanish at $`0` and such that all first derivatives of $`f` vanish at zero.
:::

Thus, it follows that there is an isomorphism
$$`\mathfrak{m}_0 / \mathfrak{m}_0^2 \cong \mathbb{R}^n \quad \text{by} \quad f \mapsto \left[ \frac{\partial f}{\partial x_1}(0), \dots, \frac{\partial f}{\partial x_n}(0) \right]`
and so the cotangent space, hence tangent space, indeed has dimension $`n`.

# Problems

:::PROBLEM "Zero-forms are functions"
Show that a differential $`0`-form on a smooth manifold $`M` is the same thing as a smooth function $`M \to \mathbb{R}`.
:::

# Formalization

:::LEANCOMPANION
:::

## Topological manifolds

Mathlib formalizes the atlas data as a `ChartedSpace`: a topological space $`M` together with a "model" topological space $`H` and, at every point of $`M`, a partial homeomorphism into $`H`.
The `chartAt` field picks out a chart through any given point.

```lean
recall ChartedSpace.chartAt
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [self : ChartedSpace H M]
    (x : M) : OpenPartialHomeomorph M H
```

For a "concrete" topological $`n`-manifold one would take $`H = \mathbb{R}^n`, but the abstract setup `ChartedSpace H M` is more flexible: we can model on $`H = \mathbb{R}^n`, on a half-space (for manifolds with boundary), or on a Banach space (for the infinite-dimensional case).

The local picture — "every point has a neighborhood looking like the model" — is guaranteed by the field `mem_chart_source`, which says every point lies in the source of the chart chosen through it.
Show it directly; applied to a point, `mem_chart_source H x` is exactly this witness.

```lean
example {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : x ∈ (chartAt H x).source := by
  sorry
```

:::solution
```lean
example {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : x ∈ (chartAt H x).source :=
  mem_chart_source H x
```
:::

## Smooth manifolds

Mathlib bundles "the topological manifold structure plus a smoothness compatibility" into the typeclass `IsManifold I n M`, where `I` is a *model with corners* — packaging the choice of model space (typically $`\mathbb{R}^n`) and any boundary structure — and `n : WithTop ℕ∞` records the smoothness order ($`C^k`, $`C^\infty`, or analytic).

```lean
recall IsManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop
```

The "transition maps are smooth" condition becomes the field saying that for any pair of charts in the atlas, the change-of-coordinates partial homeomorphism is in the $`C^n`-groupoid, which is exactly the incarnation of the requirement above.

The counterpart of a smooth map is `ContMDiff I I' n f`: for every point $`x \in M`, the local expression $`\phi_j \circ f \circ \phi_i^{-1}` is $`C^n` between the relevant open subsets of model spaces.
Constant maps are smooth, as expected.

```lean
example {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {n : WithTop ℕ∞} (c : M') : ContMDiff I I' n (fun _ : M => c) :=
  contMDiff_const
```

Now show that the identity map is smooth; the finisher is `contMDiff_id`.

```lean
example {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} :
    ContMDiff I I n (id : M → M) := by
  sorry
```

:::solution
```lean
example {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} :
    ContMDiff I I n (id : M → M) :=
  contMDiff_id
```
:::

## Regular value theorem

The regular value theorem is not yet packaged as a one-liner in Mathlib's manifold library, but its essential ingredients are.
The implicit function theorem `HasStrictFDerivAt.implicitFunction` from `Mathlib.Analysis.Calculus.Implicit` gives the chart construction at a regular point, and the "rank $`m`" hypothesis becomes surjectivity of the differential.
The smoothness of the resulting local inverse is packaged by `IsLocalDiffeomorphAt`: a map that near a point is a diffeomorphism onto its image.

Such a local diffeomorphism is in particular smooth at the point.
Prove it by drawing the smoothness out of the hypothesis, `IsLocalDiffeomorphAt.contMDiffAt`.

```lean
example {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {n : WithTop ℕ∞} {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) : ContMDiffAt I J n f x := by
  sorry
```

:::solution
```lean
example {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {n : WithTop ℕ∞} {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) : ContMDiffAt I J n f x :=
  hf.contMDiffAt
```
:::

## Differential forms on manifolds

A differential form on a manifold is a section of an exterior power of the cotangent bundle: the cotangent bundle is built as the dual of `TangentSpace I x`, and a $`k`-form is a smooth section of $`\bigwedge^k T^\ast M`.
There is no dedicated Mathlib type packaging "differential $`k`-form on a manifold" together with the chart-by-chart pullback compatibility of the definition above, so we introduce one, `ManifoldForm I M k`, as the intrinsic object those charts glue to: a pointwise assignment $`p \mapsto \alpha_p`, where each $`\alpha_p` is a continuous alternating $`k`-linear functional on the tangent space `TangentSpace I p`.

:::aside
`ManifoldForm` lives in a small `Napkin.Missing` namespace of stopgaps for objects the text defines but Mathlib does not; retire it once a de-Rham namespace lands upstream.
:::

The pointwise operations make the $`k`-forms a real vector space, and — since $`\mathtt{Fin}\ 0` is empty — a $`0`-form is exactly a scalar function `M → ℝ`, packaged by `ManifoldForm.ofScalar`.
This settles the problem "zero-forms are functions".

```lean
open ManifoldForm in
noncomputable example {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (f : M → ℝ) : ManifoldForm I M 0 := ofScalar f
```

Each $`\alpha_p` is alternating, so swapping two tangent vectors flips the sign and feeding the same vector twice returns zero; the volume form of an *orientable* manifold is a nowhere-vanishing top form, `ManifoldForm.Nonvanishing`.
Show that exhibiting one witnesses orientability, via `ManifoldForm.Orientable.of_volumeForm`.

```lean
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}
    (ω : ManifoldForm I M n) (hω : ManifoldForm.Nonvanishing ω) :
    ManifoldForm.Orientable (I := I) (M := M) n := by
  sorry
```

:::solution
```lean
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}
    (ω : ManifoldForm I M n) (hω : ManifoldForm.Nonvanishing ω) :
    ManifoldForm.Orientable (I := I) (M := M) n :=
  ManifoldForm.Orientable.of_volumeForm ω hω
```
:::

The anchor tying these forms back to calculus is the *differential* $`df` of a scalar function `f : M → ℝ`, packaged as the $`1`-form `ManifoldForm.differential f`.
Its value at $`p` on a single tangent vector is the directional derivative — the manifold derivative `mfderiv I 𝓘(ℝ) f p` applied to that vector.
Show that evaluating it reads off exactly that `mfderiv`; the finisher is `ManifoldForm.differential_eval`.

```lean
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → ℝ) (p : M) (v : Fin 1 → TangentSpace I p) :
    ManifoldForm.eval (ManifoldForm.differential f) p v
      = mfderiv I (modelWithCornersSelf ℝ ℝ) f p (v 0) := by
  sorry
```

:::solution
```lean
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → ℝ) (p : M) (v : Fin 1 → TangentSpace I p) :
    ManifoldForm.eval (ManifoldForm.differential f) p v
      = mfderiv I (modelWithCornersSelf ℝ ℝ) f p (v 0) :=
  ManifoldForm.differential_eval f p v
```
:::

The exterior derivative $`d` and the pullbacks that phrase the chart-compatibility are out of reach — the de-Rham complex is unformalized — so `ManifoldForm.ExteriorDerivative` bundles $`d`'s defining properties (degree-raising, linear, $`d^2 = 0`, and agreeing on $`0`-forms with the genuine differential $`df` via `d_ofScalar`, which rules out the trivial $`d \equiv 0`) as a hypothesis.
From that bundled data alone, the fact underlying Stokes' theorem — every exact form is closed — is derivable.
Unfold `D.Exact α` to a witness $`\alpha = d\beta`, then the $`d^2 = 0` field `D.dd` closes it.

```lean
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (D : ManifoldForm.ExteriorDerivative (I := I) (M := M)) {k : ℕ}
    {α : ManifoldForm I M (k + 1)} (h : D.Exact α) : D.Closed α := by
  sorry
```

:::solution
```lean
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (D : ManifoldForm.ExteriorDerivative (I := I) (M := M)) {k : ℕ}
    {α : ManifoldForm I M (k + 1)} (h : D.Exact α) : D.Closed α := by
  obtain ⟨β, rfl⟩ := h
  exact D.dd k β
```
:::

## Stokes' theorem for manifolds

Mathlib accommodates manifolds with boundary by allowing the model space to be a half-space rather than all of $`\mathbb{R}^n`; this is precisely the role of the "with corners" in `ModelWithCorners`.
The boundary points are then those whose chart image lies on the boundary of the half-space, captured by the predicate `ModelWithCorners.IsInteriorPoint`.

The full Stokes' theorem on a smooth oriented manifold remains an active formalization target in Mathlib; the closest currently formalized statement is the divergence theorem on a box, `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`, which corresponds to the special case $`M = [a, b] \subset \mathbb{R}^n` with the canonical orientation.

## Tangent space

Mathlib carries two complementary tangent-space constructions.
The fiber-bundle version is `TangentSpace I x`, defined as the model vector space $`E` itself (the abstract tangent vector lives in the fiber of the tangent bundle); manipulating tangent vectors algebraically goes through `Bundle.TotalSpace` and `mfderiv`.
The derivation-based version, exactly the one defined above, is `PointDerivation I x`.

```lean
recall PointDerivation
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) : Type _
```

Underneath the hood, `PointDerivation` is a special case of the algebraic `Derivation R A M`: an $`R`-linear map $`A \to M` satisfying the Leibniz rule, where here $`R = 𝕜`, $`A = C^\infty(M; 𝕜)`, and $`M = 𝕜` viewed as a module over $`A` via evaluation at $`x`.

The `mfderiv` of a map is the induced linear map on tangent spaces.
Show that the derivative of the identity map is the identity linear map; the finisher is `mfderiv_id`.

```lean
example {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    mfderiv I I (id : M → M) x
      = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  sorry
```

:::solution
```lean
example {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    mfderiv I I (id : M → M) x
      = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  mfderiv_id
```
:::

## The cotangent space

The "cotangent space as $`\mathfrak{m}/\mathfrak{m}^2`" picture is the one Mathlib carries on the algebraic-geometry side.
For a local ring `R`, the cotangent space `IsLocalRing.CotangentSpace R` is the quotient $`\mathfrak{m}/\mathfrak{m}^2` of the maximal ideal, a vector space over the residue field.

```lean
recall IsLocalRing.CotangentSpace
    (R : Type*) [CommRing R] [IsLocalRing R] : Type _
```

The smooth-manifold cotangent space is the same idea applied to $`R = C^\infty(M; \mathbb{R})`.
The sanity check that a point has trivial cotangent space when there is no room to differentiate is visible on the algebraic side: a field is a local ring whose maximal ideal is $`0`, so its cotangent space is trivial.
Show that the cotangent space of a field is a subsingleton.
The equivalence `IsLocalRing.subsingleton_cotangentSpace_iff` reads `Subsingleton (CotangentSpace R) ↔ IsField R`, so its `.mpr` direction fed `Field.toIsField K` is the finisher.

```lean
example (K : Type*) [Field K] :
    Subsingleton (IsLocalRing.CotangentSpace K) := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] :
    Subsingleton (IsLocalRing.CotangentSpace K) :=
  IsLocalRing.subsingleton_cotangentSpace_iff.mpr (Field.toIsField K)
```
:::
