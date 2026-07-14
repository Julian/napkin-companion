import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

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

:::aside
The second of these — sometimes called the "complex Liouville on a compact manifold" theorem — is exactly `MDifferentiable.exists_eq_const_of_compactSpace` in `Mathlib.Geometry.Manifold.Complex`.
It says that for a compact preconnected complex manifold $`M` with `IsManifold I 1 M` and `I.Boundaryless`, any complex-differentiable map $`f \colon M \to F` into a complex normed space $`F` is the constant function: there exists $`v \in F` with $`f = \mathrm{const}_M v`.
This generalizes the classical Liouville theorem from $`\mathbb{C}` to any compact connected complex manifold.
:::

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

This "structure-on-the-charts induces the manifold's structure" idea is exactly what `IsManifold I n M` packages: the model with corners `I` records what kind of regularity (smooth, $`C^k`, analytic, …) we want the transition maps to enjoy, and the typeclass demands that every chart of the underlying `ChartedSpace` actually agrees with that level of regularity.

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

The Mathlib incarnation is to take `IsManifold (𝓘(ℂ, ℂ)) ⊤ X`, where `𝓘(ℂ, ℂ)` is the trivial model with corners (Mathlib's name for the identity model on $`\mathbb{C}`), and the smoothness order $`\top` (denoted `ω` in some files) means "analytic".
The connectedness, Hausdorff, and second-countability constraints are extra typeclasses one would impose alongside (`PreconnectedSpace X`, `T2Space X`, `SecondCountableTopology X`).

:::aside "Maximal atlas vs. concrete atlas"
{cite}`ref:miranda` has an alternative definition, by a maximal complex atlas.
Both definitions are the same, but in practice it's easier to specify finitely many complex charts than infinitely many ones.
Mathlib's `ChartedSpace` data is the "concrete" atlas; the maximal atlas can always be recovered as `IsManifold.maximalAtlas`.
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

The Mathlib statement of "complex $`n`-manifold" is `IsManifold (𝓘(ℂ, ℂ^n)) ω M`, with model space $`E = \mathbb{C}^n`; the underlying $`(2n)`-real structure is recovered automatically because $`\mathbb{C}^n \cong \mathbb{R}^{2n}` as a real normed space.

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

The Riemann sphere is `OnePoint ℂ` in Mathlib (the one-point compactification of $`\mathbb{C}`); the complex-analytic structure on it comes from the two charts described above, and is captured by `IsManifold (𝓘(ℂ, ℂ)) ω (OnePoint ℂ)`.

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

The "any holomorphic function is constant" fact about the torus follows immediately from the Liouville-style result above: $`\mathbb{C}/L` is compact and connected, the quotient is locally biholomorphic, and so `MDifferentiable.exists_eq_const_of_compactSpace` instantiates to: every entire function on the torus is constant.

And some non-examples.

:::EXAMPLE "Disjoint union"
The disjoint union of two Riemann spheres is not a Riemann surface, because it is not connected.
:::

The condition that a Riemann surface must be connected is merely a technical condition such that theorems are nice — we don't lose much by requiring this, because any topological space with a complex structure can be broken down into a disjoint union of Riemann surfaces, one for each connected component.
