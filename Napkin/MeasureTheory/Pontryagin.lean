import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Bonus: A hint of Pontryagin duality" =>

%%%
file := "Pontryagin-duality"
%%%

In this short chapter we will give statements about how to generalize our Fourier analysis to a much wider class of groups $`G`.

# LCA groups

:::PROTOTYPE
$`\mathbb{T}`, $`\mathbb{R}`.
:::

Earlier we played with $`\mathbb{R}`, which is nice because in addition to being a topological space, it is also an abelian group under addition.
These sorts of objects which are both groups and spaces have a name.

:::DEFINITION
A group $`G` is a *topological group* is a Hausdorff topological space equipped also with a group operation $`(G, \cdot)`, such that both maps
$$`G \times G \to G \quad\text{by}\quad (x, y) \mapsto xy`
$$`G \to G \quad\text{by}\quad x \mapsto x^{-1}`
are continuous.
:::

For our Fourier analysis, we need some additional conditions.

:::DEFINITION
A *locally compact abelian (LCA) group* $`G` is one for which the group operation is abelian, and moreover the topology is *locally compact*: for every point $`p` of $`G`, there exists a compact subset $`K` of $`G` such that $`K \ni p`, and $`K` contains some open neighborhood of $`p`.
:::

Our previous examples all fall into this category:

:::EXAMPLE "Examples of locally compact abelian groups"
- Any finite group $`Z` with the discrete topology is LCA.
- The circle group $`\mathbb{T}` is LCA and also in fact compact.
- The real numbers $`\mathbb{R}` are an example of an LCA group which is *not* compact.
:::

These conditions turn out to be enough for us to define a measure on the space $`G`.
The relevant theorem, which we will just quote:

:::THEOREM "Haar measure"
Let $`G` be a locally compact abelian group.
We regard it as a measurable space using its Borel $`\sigma`-algebra $`\mathcal{B}(G)`.
There exists a measure $`\mu \colon \mathcal{B}(G) \to [0, \infty]`, called the *Haar measure*, satisfying the following properties:

- $`\mu(gS) = \mu(S)` for every $`g \in G` and measurable $`S`.
  That means that $`\mu` is "translation-invariant" under translation by $`G`.
- $`\mu(K)` is finite for any compact set $`K`.
- if $`S` is measurable, then $`\mu(S) = \inf\{\mu(U) \mid U \supseteq S \text{ open}\}`.
- if $`U` is open, then $`\mu(U) = \sup\{\mu(K) \mid K \subseteq U \text{ compact}\}`.

Moreover, it is unique up to scaling by a positive constant.
:::

:::REMARK
Note that if $`G` is compact, then $`\mu(G)` is finite (and positive).
For this reason the Haar measure on a LCA group $`G` is usually normalized so $`\mu(G) = 1`.
:::

For this chapter, we will only use the first two properties at all, and the other two are just mentioned for completeness.
Note that this actually generalizes the chapter where we constructed a measure on $`\mathcal{B}(\mathbb{R}^n)`, since $`\mathbb{R}^n` is an LCA group!

So, in short: if we have an LCA group, we have a measure $`\mu` on it.

# The Pontryagin dual

Now the key definition is:

:::DEFINITION
Let $`G` be an LCA group.
Then its *Pontryagin dual* is the abelian group
$$`\widehat{G} \overset{\text{def}}{=} \{\text{continuous group homomorphisms } \xi \colon G \to \mathbb{T}\}.`
The maps $`\xi` are called *characters*.
It can be itself made into an LCA group.
:::

:::EXAMPLE "Examples of Pontryagin duals"
- $`\widehat{\mathbb{Z}} \cong \mathbb{T}`, since group homomorphisms $`\mathbb{Z} \to \mathbb{T}` are determined by the image of $`1`.
- $`\widehat{\mathbb{T}} \cong \mathbb{Z}`.
  The characters are given by $`\theta \mapsto n\theta` for $`n \in \mathbb{Z}`.
- $`\widehat{\mathbb{R}} \cong \mathbb{R}`.
  This is because a nonzero continuous homomorphism $`\mathbb{R} \to S^1` is determined by the fiber above $`1 \in S^1`.
  (Algebraic topologists might see covering projections here.)
- $`\widehat{\mathbb{Z}/n\mathbb{Z}} \cong \mathbb{Z}/n\mathbb{Z}`, characters $`\xi` being determined by the image $`\xi(1) \in \mathbb{T}`.
- $`\widehat{G \times H} \cong \widehat{G} \times \widehat{H}`.
:::

:::EXERCISE "$`\\widehat{Z} \\cong Z`, for finite abelian Z"
If $`Z` is a finite abelian group, show that $`\widehat{Z} \cong Z`, using the results of the previous example.
You may now recognize that the bilinear form $`\cdot \colon Z \times Z \to \mathbb{T}` is exactly a choice of isomorphism $`Z \to \widehat{Z}`.
It is not "canonical".
:::

True to its name as the dual, and in analogy with $`(V^\vee)^\vee \cong V` for vector spaces $`V`, we have:

:::THEOREM "Pontryagin duality theorem"
For any LCA group $`G`, there is an isomorphism
$$`G \cong \widehat{\widehat{G}} \qquad \text{by} \qquad x \mapsto (\xi \mapsto \xi(x)).`
:::

The compact case is especially nice.

:::PROPOSITION "$`G` compact iff $`\\widehat{G}` discrete"
Let $`G` be an LCA group.
Then $`G` is compact if and only if $`\widehat{G}` is discrete.
:::

:::PROOF
See the LCA-compact problem at the end of the chapter.
:::

# The orthonormal basis in the compact case

Let $`G` be a compact LCA group, and work with its Haar measure.
We may now let $`L^2(G)` be the space of square-integrable functions to $`\mathbb{C}`, i.e.
$$`L^2(G) = \left\{f \colon G \to \mathbb{C} \quad\text{such that}\quad \int_G |f|^2 < \infty\right\}.`
Thus we can equip it with the inner form
$$`\langle f, g \rangle = \int_G f \cdot \overline{g}.`

In that case, we get all the results we wanted before:

:::THEOREM "Characters of $`\\widehat{G}` form an orthonormal basis"
Assume $`G` is LCA and compact (so $`\widehat{G}` is discrete).
Then the characters
$$`(e_\xi)_{\xi \in \widehat{G}} \qquad\text{by}\qquad e_\xi(x) = e(\xi(x)) = \exp(2\pi i \xi(x))`
form an orthonormal basis of $`L^2(G)`.
Thus for each $`f \in L^2(G)` we have
$$`f = \sum_{\xi \in \widehat{G}} \widehat{f}(\xi) e_\xi`
where
$$`\widehat{f}(\xi) = \langle f, e_\xi \rangle = \int_G f(x) \exp(-2\pi i \xi(x)) \; d\mu.`
:::

The sum $`\sum_{\xi \in \widehat{G}}` makes sense since $`\widehat{G}` is discrete.
In particular,

- Letting $`G = Z` for a finite group $`G` gives "Fourier transform on finite groups".
- The special case $`G = \mathbb{Z}/n\mathbb{Z}` has its own well-known name: the "discrete Fourier transform".
- Letting $`G = \mathbb{T}` gives the "Fourier series".

# The Fourier transform of the non-compact case

If $`G` is LCA but not compact, then the orthonormal-basis theorem becomes false.
On the other hand, it's still possible to define $`\widehat{G}`.
We can then try to write the Fourier coefficients anyways: let
$$`\widehat{f}(\xi) = \int_G f \cdot \overline{e_\xi} \; d\mu`
for $`\xi \in \widehat{G}` and $`f \colon G \to \mathbb{C}`.
The results are less fun in this case, but we still have, for example:

:::THEOREM "Fourier inversion formula in the non-compact case"
Let $`\mu` be a Haar measure on $`G`.
Then there exists a unique Haar measure $`\nu` on $`\widehat{G}` (called the *dual measure*) such that: whenever $`f \in L^1(G)` and $`\widehat{f} \in L^1(\widehat{G})`, we have
$$`f(x) = \int_{\widehat{G}} \widehat{f}(\xi) \xi(x) \; d\nu`
for almost all $`x \in G` (with respect to $`\mu`).
If $`f` is continuous, this holds for all $`x`.
:::

So while we don't have the niceness of a full inner product from before, we can still in some situations at least write $`f` as integral in sort of the same way as before.

In particular, they have special names for a few special $`G`:

- If $`G = \mathbb{R}`, then $`\widehat{G} = \mathbb{R}`, yielding the "(continuous) Fourier transform".
- If $`G = \mathbb{Z}`, then $`\widehat{G} = \mathbb{T}`, yielding the "discrete time Fourier transform".

# Summary

We summarize our various flavors of Fourier analysis from the previous sections in the following table.
In the first part $`G` is compact, in the second half $`G` is not.
$$`\begin{array}{llll} \hline \text{Name} & \text{Domain } G & \text{Dual } \widehat{G} & \text{Characters} \\ \hline \text{Binary Fourier analysis} & \{\pm 1\}^n & S \subseteq \{1, \dots, n\} & \prod_{s \in S} x_s \\ \text{Fourier transform on finite groups} & Z & \xi \in \widehat{Z} \cong Z & e(i \xi \cdot x) \\ \text{Discrete Fourier transform} & \mathbb{Z}/n\mathbb{Z} & \xi \in \mathbb{Z}/n\mathbb{Z} & e(\xi x / n) \\ \text{Fourier series} & \mathbb{T} \cong [-\pi, \pi] & n \in \mathbb{Z} & \exp(inx) \\ \hline \text{Continuous Fourier transform} & \mathbb{R} & \xi \in \mathbb{R} & e(\xi x) \\ \text{Discrete time Fourier transform} & \mathbb{Z} & \xi \in \mathbb{T} \cong [-\pi, \pi] & \exp(i \xi n) \\ \end{array}`

You might notice that the *various names are awful*.
This is part of the reason I got confused as a high school student: every type of Fourier series above has its own Wikipedia article.
If it were up to me, we would just use the term "$`G`-Fourier transform", and that would make everyone's lives a lot easier.

# Problems

:::PROBLEM
If $`G` is compact, so $`\widehat{G}` is discrete, describe the dual measure $`\nu`.
:::

It is the counting measure (matching the discrete sum $`\sum_{\xi \in \widehat{G}}` in the orthonormal-basis theorem).

:::PROBLEM "LCA compactness duality"
Show that an LCA group $`G` is compact if and only if $`\widehat{G}` is discrete.
(You will need the compact-open topology for this.)
:::

# Formalization

:::LEANCOMPANION
:::

## LCA groups

Mathlib's `IsTopologicalGroup G` is the typeclass bundling a `Group G` and a `TopologicalSpace G` with continuity of multiplication and inversion.
The Hausdorff condition is *not* baked in by default; you add `[T2Space G]` separately when you need it.

```lean
example (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : True := trivial
```

An LCA group is then assembled from `[CommGroup G]`, `[TopologicalSpace G]`, `[IsTopologicalGroup G]`, and `[LocallyCompactSpace G]`.
Here `Circle` is the unit circle in $`\mathbb{C}` with its multiplicative group structure, the abelian topological group $`\mathbb{T}`, while $`\mathbb{R}`, $`\mathbb{Z}`, and `ZMod n` all carry the LCA-group instances out of the box.

The Haar measure is built through `MeasureTheory.Measure.haarMeasure`, which takes a nonempty compact set as a normalization datum and produces a translation-invariant measure on the group.

```lean
noncomputable example {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (K : TopologicalSpace.PositiveCompacts G) :
    MeasureTheory.Measure G :=
  MeasureTheory.Measure.haarMeasure K
```

The theorem's four properties unpack into `MeasureTheory.map_mul_left_eq_self` for translation invariance, `IsCompact.measure_lt_top` for compact-set finiteness, and the outer/inner regularity classes for the last two; uniqueness up to scaling is `MeasureTheory.Measure.haarMeasure_unique`.
As a first exercise, show that the defining translation invariance $`\mu(gS) = \mu(S)` really holds: pushing a left-invariant measure forward along left multiplication by $`g` recovers $`\mu`.

```lean
example {G : Type*} [Group G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant]
    (g : G) : μ.map (g * ·) = μ := by
  sorry
```

## The Pontryagin dual

`PontryaginDual G` is Mathlib's type of characters, defined as `G →ₜ* Circle`: the continuous group homomorphisms into the unit circle, given the compact-open topology and pointwise multiplication that make it into another LCA group.

```lean
example (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Type _ := PontryaginDual G
```

The double-duality isomorphism $`G \cong \widehat{\widehat{G}}` is not yet packaged for a general LCA group; the finite abelian case is available as `AddChar.doubleDualEquiv`, between a finite abelian group and the characters of its characters.
One half of the "compact iff discrete" proposition is, however, already an instance: when $`G` is compact its dual is discrete.
Confirm it.

```lean
example (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] :
    DiscreteTopology (PontryaginDual G) := by
  sorry
```

## The orthonormal basis in the compact case

$`L^2(G)` is `MeasureTheory.Lp ℂ 2 μ`, the quotient of square-integrable functions by almost-everywhere equality, and its canonical inner product is exactly the integral of the pointwise inner products.

```lean
example {α E : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g : MeasureTheory.Lp E 2 μ) :
    inner ℂ f g = ∫ a, inner ℂ (f a) (g a) ∂μ :=
  MeasureTheory.L2.inner_def f g
```

For the circle $`\mathbb{T}` the characters really do form an orthonormal family, recorded as `orthonormal_fourier` against the family `fourierLp`.
State this orthonormality.

```lean
example {T : ℝ} [Fact (0 < T)] :
    Orthonormal ℂ (fourierLp (T := T) 2) := by
  sorry
```

## The Fourier transform of the non-compact case

Mathlib's Fourier transform is `VectorFourier.fourierIntegral`, parametrized by a bilinear pairing `L` and a character; the concrete real transform picks the character `Real.fourierChar`.

```lean
noncomputable example {V W E : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (μ : MeasureTheory.Measure V)
    (f : V → E) : W → E :=
  VectorFourier.fourierIntegral Real.fourierChar μ L f
```

The inversion formula holds on a finite-dimensional real inner product space such as $`\mathbb{R}`, as `MeasureTheory.Integrable.fourierInv_fourier_eq` (pointwise) and `Continuous.fourierInv_fourier_eq` (everywhere); the general-LCA statement is not yet in Mathlib.
Prove the everywhere version: for a continuous integrable $`f` with integrable transform, applying $`\mathcal{F}` then $`\mathcal{F}^{-1}` recovers $`f`.

```lean
open scoped FourierTransform in
example {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : V → E) (h : Continuous f) (hf : MeasureTheory.Integrable f)
    (h'f : MeasureTheory.Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f := by
  sorry
```

## Summary

Mathlib essentially follows the "$`G`-Fourier transform" wish: one `VectorFourier.fourierIntegral` definition is parametrized by the group, the measure, the pairing `L`, and an `AddChar`-valued character landing in `Circle`, and the named flavors above are all special cases.
As a worked closing note, the transform is linear: scaling the input scales the output.

```lean
example {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (μ : MeasureTheory.Measure V)
    (f : V → E) (r : ℂ) :
    VectorFourier.fourierIntegral Real.fourierChar μ L (r • f)
      = r • VectorFourier.fourierIntegral Real.fourierChar μ L f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _
```
