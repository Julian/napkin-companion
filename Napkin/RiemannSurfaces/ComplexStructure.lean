import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Napkin.Missing.RiemannSphere

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open scoped Manifold Topology OnePoint

open Napkin
open Napkin.Missing

set_option pp.rawOnError true

#doc (Manual) "Basic definitions of Riemann surfaces" =>

%%%
file := "Riemann-surfaces"
%%%

Roughly speaking, the theory of Riemann surfaces is just the generalization of complex analysis using ideas from differential geometry: just like how a $`2`-manifold can be viewed as a collection of patches of the real plane $`\mathbb{R}^2` smoothly welded together to form a more complicated object, we take "pieces" of the complex plane $`\mathbb{C}`, *analytically* welded together.

We already know that the theory of holomorphic function is very nice — they're all analytic!
The same amount of rigidity is to be expected here.

In fact, on *compact* Riemann surfaces, the theories are even nicer than the case of holomorphic functions!
For example:

- For two Riemann surfaces $`X` and $`Y` where $`Y` is compact, any meromorphic function $`f \colon X \to Y` must in fact be holomorphic, i.e. defined everywhere.
- If $`X` is a compact Riemann surface, then a holomorphic function $`f \colon X \to \mathbb{C}` is constant.
- In the same setting as above, furthermore we have that if $`g \colon X \to \mathbb{C}` is meromorphic, then the number of zeros of $`g` is equal to the number of poles of $`g`, with multiplicity.

:::REMARK "Why do we have these nice properties?"
Roughly speaking, $`\mathbb{C}` is not compact — it is isomorphic to the Riemann sphere with a hole removed.
By filling in the hole, we allow meromorphic functions to be extended taking value $`\infty` at places that previously were a pole.
:::

As an orientable $`2`-manifold, we can define the *genus* of a Riemann surface — it is a purely topological concept, yet it is crucially linked to several algebraic invariants in very surprising ways.
You may have heard of the *elliptic curve* in cryptography — they also present as a Riemann surface, and a generalization, *hyperelliptic curve*, form a family of Riemann surfaces of arbitrary genus $`\geq 2`!

# Complex structures

Recall the definitions in the previous chapters:

- A topological $`n`-manifold is a Hausdorff space, with a covering $`\{U_i\}`, each being homeomorphic to $`\mathbb{R}^n`.
- A smooth $`n`-manifold is a topological $`n`-manifold, where all the transition maps are smooth.

What do they have in common?
Seemingly not too much.
But essentially, they're all describing the same philosophy:

:::MORAL
We take countably many patches $`\{U_i\}`, and weld them together while keeping the underlying structure.
:::

Here, a topological manifold has a *topological structure*, and a smooth manifold has a *smooth structure*.
In a similar manner, a complex manifold has a *complex structure*.

What do we mean by "structure" here?

First, a topological structure is familiar to you — it's just a topology.
Formally, the topology is defined by the collection of open sets, but the actual *meaning* of a topological structure dictates:

- whether a set is considered open or closed,
- whether a sequence of points converges to a given point,
- whether a map $`X \to Y` or $`Y \to X` is continuous (given $`Y` is another topological space),
- etc.

Given a topological $`n`-manifold with an existing (Hausdorff) topology on it, we can tell whether a local chart *respects the topological structure*; in other words, is a homeomorphism.

:::EXAMPLE "(0, 2) is a topological 1-manifold"
The open interval $`(0, 2)` included in $`\mathbb{R}` can be considered a topological manifold.
Two possible charts for the space, $`\phi_1` and $`\phi_2`, are given by
$$`\phi_1 \colon (0, 2) \to (0, 2), \quad \phi_1(x) = x`
and
$$`\phi_2 \colon (0, 2) \to (0, 1.3), \quad \phi_2(x) = x + 0.35 \cdot (1 - x - |1 - x|).`
:::

:::figure "figures/riemann-surfaces/complex-structure-charts-linear.svg"
Two charts $`\phi_1`, $`\phi_2` of $`(0, 2)`, glued over their overlap in $`\mathbb{R}`; the chart $`\phi_2` is a homeomorphism but does not look smooth.
:::

In the example above, you may notice that, even though the chart $`\phi_2` is a homeomorphism, it doesn't look *smooth*.
So, you want to define a smooth $`2`-manifold as something like:

> A surface $`S \subseteq \mathbb{R}^3` is a smooth $`2`-manifold if, for each $`p \in S`, there exists an open neighborhood $`V \subseteq S` that is diffeomorphic to $`E \subseteq \mathbb{R}^2`.

In fact, this is the actual definition in classical differential geometry — of course, this isn't completely general, for instance, we know that the Klein bottle cannot be embedded into $`\mathbb{R}^3`.

So why didn't we define something like this in the previous chapter?
The problem is, the concept of a diffeomorphism isn't defined on a Hausdorff topological space — in fact it can't be defined: in the example above, you can see a homeomorphism that is not a diffeomorphism — in other words, a topological space can be assigned different *smooth structures*.

So, the essence of what the smooth-manifold definition is doing is, it implicitly defines what a *smooth structure* means, by inducing the smooth structure from each patch $`E_i \subseteq \mathbb{R}^n` to the topological space $`M`.
The condition that the transition functions need to be smooth is, of course, to ensure that the smooth structures on $`M` induced by different $`\phi_i` are the same.

In completely the same way, we could have defined a topological manifold by:

> A topological $`n`-manifold $`M` is a set with a collection of subsets $`\{U_i\}` that covers $`M`, for each $`U_i` there is a bijective map from it to a subset of $`\mathbb{R}^n`, say
> $$`\phi_i \colon U_i \to E_i \subseteq \mathbb{R}^n`
> where each $`E_i` is an open subset of $`\mathbb{R}^n`, satisfying that all the transition maps are topological homeomorphisms.

Here, the $`\phi_i` are "set isomorphisms" and play a similar role as the homeomorphisms; the topological space structure is similarly induced from the patches $`E_i`.

:::EXAMPLE "(0, 2) is also a smooth 1-manifold"
Just as above, the open interval $`(0, 2)` included in $`\mathbb{R}` can also be considered a smooth manifold.
This time around, $`\phi_1` is the same as above, but
$$`\phi_2 \colon (0, 2) \to \left(0, 2 + \tfrac{1}{e}\right)`
is defined by
$$`\phi_2(x) = \begin{cases} x & \text{if } x \leq 1 \\ x + e^{-1/(x-1)} & \text{otherwise.} \end{cases}`
Because all of $`\phi_1`, $`\phi_2`, and their inverses are smooth functions, the transition maps $`\phi_1 \circ \phi_2^{-1}` and $`\phi_2 \circ \phi_1^{-1}` are thus smooth.
:::

:::figure "figures/riemann-surfaces/complex-structure-charts-smooth.svg"
Here the chart $`\phi_2` is smooth — flat to infinite order at the overlap edge — so the transition maps are smooth.
:::

You should take a moment to think through this idea — because smooth functions on $`\mathbb{R}^n` are so natural, it's easy to forget that a smooth manifold carries more structure than just the topology.

Once again, as we have seen in the example above, $`\mathbb{R}^n` has more structure than just being smooth — it has an *analytic structure*.
The chart $`\phi_2` does not preserve this structure.

So, for Riemann surfaces, we will just have:

:::MORAL
A Riemann surface is a smooth (real) $`2`-manifold which locally looks like $`\mathbb{C}`, and carries an *complex-smooth structure*.
:::

Of course, by the miracle of complex analysis — holomorphic functions are analytic — this is equivalent to stating that a Riemann surface carries a complex-analytic structure.

# Riemann surface

:::PROTOTYPE
The Riemann sphere, or any open subset of $`\mathbb{C}` such as $`\{z \in \mathbb{C} \mid |z| < 1\}`.
:::

From the motivation above, the definition of a Riemann surface naturally falls out:

:::DEFINITION "Riemann surface"
A *Riemann surface* $`X` is a second-countable connected Hausdorff space with an open cover $`\{U_i\}` of countably many sets homeomorphic to open subsets of $`\mathbb{C}`, say by homeomorphisms
$$`\phi_i \colon U_i \xrightarrow{\cong} E_i \subseteq \mathbb{C}`
such that the *transition maps* $`\phi_{ij}` defined by
$$`\phi_{ij} \colon E_i \cap \phi_i(U_i \cap U_j) \xrightarrow{\phi_i^{-1}} U_i \cap U_j \xrightarrow{\phi_j} E_j \cap \phi_j(U_i \cap U_j)`
are analytic functions.
Each $`\phi_i` is called a *complex chart*, and together they form a *complex atlas*.
:::

We say that the complex atlas gives the Hausdorff space a *complex structure*.
Thus, in other words, a Riemann surface is a (second-countable, connected, Hausdorff) topological space with a complex structure.

:::aside "Maximal atlas vs. concrete atlas"
{cite}`ref:miranda` has an alternative definition, by a maximal complex atlas.
Both definitions are the same, but in practice it's easier to specify finitely many complex charts than infinitely many ones.
:::

A complex chart $`U_i \to E_i` should be thought of as giving a *local coordinate* on $`U_i`.
Formally:

:::DEFINITION "Local coordinate"
For a point $`p \in X`, open set $`U \subseteq X` and complex chart $`\phi \colon U \to \mathbb{C}`, let $`z = \phi(x)` for each $`x \in U`; we call $`z` a *local coordinate*.
We say that the local coordinate is *centered* at $`p` if $`\phi(p) = 0`.
:::

# Complex manifold

Analogously to the definition of a real $`n`-manifold, we can define a complex manifold.
Just as above, the structure has much more rigidity than a smooth surface.

:::DEFINITION "Complex n-manifold"
A *complex $`n`-manifold* is a Hausdorff space with an open cover $`\{U_i\}` of countably many sets homeomorphic to open subsets of $`\mathbb{C}^n`, say by homeomorphisms
$$`\phi_i \colon U_i \xrightarrow{\cong} E_i \subseteq \mathbb{C}^n`
such that the *transition maps* $`\phi_{ij}` are analytic functions.
:::

Of course, a complex $`n`-manifold is naturally a smooth (real) $`2n`-manifold.

# Examples of Riemann surfaces

In this chapter, several examples will be given.

:::EXAMPLE "Open subsets of ℂ"
Any connected open subset $`U \subseteq \mathbb{C}` is a Riemann surface, with the single chart given by the inclusion $`U \hookrightarrow \mathbb{C}`.
This is a boring example (the whole thing can be defined without any welding), but let's go on.
:::

:::figure "figures/riemann-surfaces/complex-structure-open-set.svg"
Any connected open subset $`U \subseteq \mathbb{C}` is a Riemann surface.
:::

::::EXAMPLE "The Riemann sphere"
The Riemann sphere $`\mathbb{C}_\infty`, as a smooth $`2`-manifold, is just a sphere.

:::figure "figures/riemann-surfaces/complex-structure-riemann-sphere.svg"
The Riemann sphere $`\mathbb{C}_\infty`, a smooth $`2`-manifold.
:::

Its complex structure is defined as follows.

Embed the sphere in $`\mathbb{R}^3` such that $`N = (0, 0, 1)` and $`S = (0, 0, 0)` are two antipodal points.
Let $`E_1` be the $`xy`-plane, and let $`E_2` be the set of points with $`z = 1`.

Then let $`\phi_1 \colon \mathbb{C}_\infty \setminus \{N\} \to E_1` be the stereographic projection from the sphere (except the point $`N`) to $`E_1` through the point $`N`, and let $`\phi_2 \colon \mathbb{C}_\infty \setminus \{S\} \to E_2` be the stereographic projection from the sphere (except the point $`S`) to $`E_2` through the point $`S`.

We think of $`E_1` and $`E_2` as copies of the complex plane embedded in $`\mathbb{R}^3` by $`z \mapsto (\Re z, \Im z, 0) \in E_1` and $`t \mapsto (\Re t, -\Im t, 1) \in E_2`.
Then $`\phi_1` and $`\phi_2` are complex charts for $`\mathbb{C}_\infty`.

The domains of $`\phi_1` and $`\phi_2` cover $`\mathbb{C}_\infty`.
To make $`\mathbb{C}_\infty` into a complex manifold, we must ensure that the complex structures induced by $`\phi_1` and $`\phi_2` agree — indeed, over any open set $`U` that contains neither $`N` nor $`S`, the projections are related by $`\phi_1(p) = \frac{1}{\phi_2(p)}` for all $`p \in U`.

This also explains why the minus sign is needed in $`t \mapsto (\Re t, -\Im t, 1)` — otherwise, the projections would be related by $`\phi_1(p) = \frac{1}{\overline{\phi_2(p)}}`, which is not analytic.

We can think of the Riemann sphere as the result of welding two copies of $`\mathbb{C}` together in order to "fill in" the missing point $`\infty`.
::::

In the example above, the local coordinate given by $`\phi_1` is centered at $`S`, and the local coordinate given by $`\phi_2` is centered at $`N`.
The point $`\phi_1^{-1}(4)` would have local coordinate $`z = 4` under the chart $`\phi_1`, and local coordinate $`t = \frac{1}{4}` under the chart $`\phi_2`.

::::EXAMPLE "The complex torus"
Let $`L` be the set $`\mathbb{Z}[i]` of complex numbers with both real and imaginary parts integers.
Then $`L` forms an additive subgroup of $`\mathbb{C}`.

Consider the quotient $`\mathbb{C}/L`.
The quotient map $`\mathbb{C} \to \mathbb{C}/L` induces a natural complex structure on $`\mathbb{C}/L`.

Picture $`\mathbb{C}/L` as a unit square; the top and bottom edges, as well as the left and right edges, are smoothly welded together.

:::figure "figures/riemann-surfaces/complex-structure-lattice-quotient.svg"
The lattice $`L` in $`\mathbb{C}` with its unit-square fundamental domain, and the quotient torus $`\mathbb{C}/L`.
:::

For each small patch of the torus, we can isomorphically map it to $`\mathbb{C}` by taking a suitable component of the preimage of the quotient map — the different choices of the projection are related by transition functions $`\phi_{ij}(x) = x + a` for $`a \in L`, and this is analytic.

The complex torus is compact, thus any holomorphic function on $`\mathbb{C}/L` is constant.
Meromorphic functions are more interesting, and also difficult to construct.
::::

And some non-examples.

:::EXAMPLE "Disjoint union"
The disjoint union of two Riemann spheres is not a Riemann surface, because it is not connected.
:::

The condition that a Riemann surface must be connected is merely a technical condition such that theorems are nice — we don't lose much by requiring this, because any topological space with a complex structure can be broken down into a disjoint union of Riemann surfaces, one for each connected component.

# Formalization

:::LEANCOMPANION
:::

## Complex structures

The "structure-on-the-charts induces the manifold's structure" idea is exactly what `IsManifold I n M` packages.
The *model with corners* `I` records what kind of regularity — smooth, $`C^k`, analytic, … — the transition maps must enjoy, while the underlying `ChartedSpace H M` supplies the atlas of charts modelled on `H`.
The predicate `IsManifold I n M` then demands that every chart is compatible to order `n`.

The model space is always a manifold over its own trivial model with corners `𝓘(ℂ, ℂ)`, at the analytic regularity `ω`.
This regularity index reads `ω` for analytic ($`C^\omega`) and a natural number `n` for `n`-times continuously differentiable ($`C^n`); the Liouville examples below drop to `1`.
So the complex plane $`\mathbb{C}` carries the tautological complex structure.

```lean
example : IsManifold (𝓘(ℂ, ℂ)) ω ℂ := inferInstance

example : Nonempty (ChartedSpace ℂ ℂ) := ⟨inferInstance⟩
```

The same reasoning applies over $`\mathbb{R}`: the real line is a manifold over its trivial model.
Confirm it; as over $`\mathbb{C}`, `inferInstance` supplies the structure.

```lean
example : IsManifold (𝓘(ℝ, ℝ)) ω ℝ := by
  sorry
```

## Riemann surfaces

A Riemann surface is `IsManifold (𝓘(ℂ, ℂ)) ω X`, where `𝓘(ℂ, ℂ)` is the trivial model with corners on $`\mathbb{C}`, and the regularity order `ω` means "analytic".
The connectedness, Hausdorff, and second-countability constraints are recorded separately, as `PreconnectedSpace X`, `T2Space X`, and `SecondCountableTopology X`.
The concrete atlas is the data of the `ChartedSpace ℂ X`; the maximal atlas is recovered as `IsManifold.maximalAtlas`, and the concrete charts always live inside it.

```lean
example (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] (p : X) :
    chartAt ℂ p ∈ IsManifold.maximalAtlas (𝓘(ℂ, ℂ)) ω X :=
  IsManifold.chart_mem_maximalAtlas p
```

Show that every chart in the concrete atlas is a member of the maximal atlas; the set-level counterpart of the lemma above is `IsManifold.subset_maximalAtlas`.

```lean
example (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    atlas ℂ X ⊆ IsManifold.maximalAtlas (𝓘(ℂ, ℂ)) ω X := by
  sorry
```

## Complex manifolds

A complex $`n`-manifold is `IsManifold (𝓘(ℂ, (Fin n → ℂ))) ω M`, with model space $`E = \mathbb{C}^n` realized as `Fin n → ℂ`.
The underlying real $`(2n)`-dimensional structure comes for free, since $`\mathbb{C}^n \cong \mathbb{R}^{2n}` as a real normed space.
The model space itself is the first example.

```lean
example (n : ℕ) : IsManifold (𝓘(ℂ, (Fin n → ℂ))) ω (Fin n → ℂ) := inferInstance
```

At $`n = 1` this recovers a one-dimensional complex model, i.e. a Riemann-surface chart.
Confirm it; `inferInstance` closes it just as at general $`n`.

```lean
example : IsManifold (𝓘(ℂ, (Fin 1 → ℂ))) ω (Fin 1 → ℂ) := by
  sorry
```

## Examples of Riemann surfaces

The Riemann sphere is the one-point compactification `OnePoint ℂ`, welded from the two stereographic charts described above.
Mathlib equips `OnePoint ℂ` with its topology but not with a `ChartedSpace ℂ` or `IsManifold (𝓘(ℂ, ℂ)) ω` structure, so the sphere's complex-manifold *instance* cannot be exhibited.
The two charts and the analytic weld between them can be built explicitly, though: `Napkin.Missing.RiemannSphere` records the two chart domains, the two coordinate maps, and the holomorphic transition, retiring the day `OnePoint ℂ` becomes a complex manifold upstream.

The first chart's domain `sphereChart0Dom` is the copy of $`\mathbb{C}` inside `OnePoint ℂ` (every point but $`\infty`), with coordinate `sphereChart0` sending $`\uparrow z \mapsto z`.
The second chart's domain `sphereChart1Dom` is $`(\mathbb{C} \setminus \{0\}) \cup \{\infty\}` (every point but $`\uparrow 0`), and its coordinate `sphereChart1` sends $`\uparrow z \mapsto z^{-1}` — in particular filling in the hole, $`\infty \mapsto 0`.

```lean
example (z : ℂ) : sphereChart0 ↑z = z := rfl
example (z : ℂ) : sphereChart1 ↑z = z⁻¹ := rfl
example : sphereChart1 ∞ = 0 := rfl
```

On the overlap $`\mathbb{C} \setminus \{0\}` the coordinate $`z` of the first chart and the coordinate $`w` of the second are related by the transition $`w = z^{-1}`, which is `sphereTransition`.
It is its own inverse, since $`(z^{-1})^{-1} = z`.

```lean
example : Function.Involutive sphereTransition :=
  sphereTransition_involutive
```

The whole point of the weld is that this transition is *holomorphic* away from $`0`: it is analytic on a neighborhood of every point of $`\mathbb{C} \setminus \{0\}`.
`AnalyticOnNhd ℂ g s` records exactly this — that `g` is analytic on a neighborhood of every point of `s` — and the prototype is inversion itself, `analyticOnNhd_inv`.

```lean
example : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} :=
  analyticOnNhd_inv
```

The transition `sphereTransition` is that very map $`z \mapsto z^{-1}`, so the same fact carries over, packaged in the shim as `sphereTransition_analyticOnNhd`.
Confirm it.

```lean
example : AnalyticOnNhd ℂ sphereTransition {z : ℂ | z ≠ 0} := by
  sorry
```

The two chart domains cover the sphere: the only point outside `sphereChart0Dom` is $`\infty`, which lies in `sphereChart1Dom`.
Show that every point lies in one chart or the other, and that $`\infty` in particular lands in the second chart but not the first; the shim proves these as `sphere_charts_cover`, `infty_mem_sphereChart1Dom`, and `infty_notMem_sphereChart0Dom`.

```lean
example (p : OnePoint ℂ) :
    p ∈ sphereChart0Dom ∨ p ∈ sphereChart1Dom := by
  sorry

example : (∞ : OnePoint ℂ) ∈ sphereChart1Dom ∧
    (∞ : OnePoint ℂ) ∉ sphereChart0Dom := by
  sorry
```

Bundling this data — a covering family of charts whose transitions are analytic on their overlaps — is the text's Definition of a complex atlas, recorded as `ComplexAtlas`.
The sphere's two-chart atlas, indexed by `Bool`, is `riemannSphereAtlas`.

```lean
noncomputable example : ComplexAtlas (OnePoint ℂ) := riemannSphereAtlas
```

The "any holomorphic function on a compact surface is constant" fact is the manifold analogue of Liouville's theorem: `MDifferentiable.exists_eq_const_of_compactSpace` says that a complex-differentiable map from a compact preconnected complex manifold into a complex normed space is the constant function.
Applied to the complex torus $`\mathbb{C}/L` — compact and connected — this forces every holomorphic function on it to be constant.
The regularity index is `1` here rather than the analytic `ω` used above, since the statement already holds at $`C^1`.

```lean
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (𝓘(ℂ, ℂ)) 1 M] [CompactSpace M] [PreconnectedSpace M]
    (f : M → F) (hf : MDifferentiable (𝓘(ℂ, ℂ)) (𝓘(ℂ, F)) f) :
    ∃ v : F, f = Function.const M v :=
  hf.exists_eq_const_of_compactSpace
```

Deduce the "takes equal values" form: a holomorphic function on a compact connected complex manifold agrees at any two points.
Extract the constant `v` with `hf.exists_eq_const_of_compactSpace`, then both values are `v`.

```lean
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (𝓘(ℂ, ℂ)) 1 M] [CompactSpace M] [PreconnectedSpace M]
    (f : M → F) (hf : MDifferentiable (𝓘(ℂ, ℂ)) (𝓘(ℂ, F)) f) (a b : M) :
    f a = f b := by
  sorry
```

## Removable singularities

The idea of "filling in the hole" — extending a function across a puncture — is Riemann's removable singularity theorem.
In its weak form, `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` says that a function differentiable on a punctured neighborhood of a point and merely continuous at the point is in fact analytic there.

```lean
example {f : ℂ → ℂ} {c : ℂ} (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hc : ContinuousAt f c) : AnalyticAt ℂ f c :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc
```

Show the packaged equivalence: on a neighborhood of $`c`, being differentiable off $`c` together with continuity at $`c` is the same as being differentiable on the whole neighborhood.
This bundled iff is `Complex.differentiableOn_compl_singleton_and_continuousAt_iff`, whose forward direction at a single point is the worked lemma above.

```lean
example {f : ℂ → ℂ} {s : Set ℂ} {c : ℂ} (hs : s ∈ 𝓝 c) :
    DifferentiableOn ℂ f (s \ {c}) ∧ ContinuousAt f c ↔
      DifferentiableOn ℂ f s := by
  sorry
```
