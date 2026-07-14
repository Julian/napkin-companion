import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Application of cohomology" =>

%%%
file := "Application-of-cohomology"
%%%

In this final chapter on topology, I'll state (mostly without proof) some nice properties of cohomology groups, and in particular introduce the so-called cup product.
For an actual treatise on the cup product, see {cite}`ref:hatcher`.

As mentioned in the previous chapter, you can put all the cohomology groups $`H^\bullet(X)` together to form the _cohomology ring_, which gives more structure than the case of homology — enough structure to allow distinguishing between $`\mathbb{CP}^2` and $`S^2 \vee S^4`, or between $`\mathbb{CP}^3` and $`S^2 \times S^4`.

Even though the description above is completely non-descriptive (it doesn't give you insight into _what_ the structure is about), and actually, some people would say:

:::quote
It does not matter what homology measures intuitively, as it is a convenient tool that takes something very difficult (topology) and turns it into something simple (abelian group).
:::

Nevertheless, it is interesting that the cup product _is actually visualizable_!
At least when the dimension does not exceed $`3`.

# Poincaré duality

First cool result: you may have noticed symmetry in the (co)homology groups of "nice" spaces like the torus or $`S^n`.
In fact this is predicted by:

:::THEOREM "Poincaré duality"
If $`M` is a smooth oriented compact $`n`-manifold, then we have a natural isomorphism $$`H^k(M; \mathbb{Z}) \cong H_{n-k}(M)`
for every $`k`.
In particular, $`H^k(M) = 0` for $`k > n`.
:::

So for smooth oriented compact manifolds, cohomology and homology groups are not so different.
From this follows the symmetry that we mentioned when we first defined the Betti numbers:

:::COROLLARY "Symmetry of Betti numbers"
Let $`M` be a smooth oriented compact $`n`-manifold, and let $`b_k` denote its Betti number.
Then $`b_k = b_{n-k}`.
:::

# de Rham cohomology

We now reveal the connection between differential forms and singular cohomology.

Let $`M` be a smooth manifold.
We specialize to the case $`G = \mathbb{R}`, the additive group of real numbers.

:::QUESTION
Check that $`\operatorname{Ext}(H, \mathbb{R}) = 0` for any finitely generated abelian group $`H`.
:::

Thus, with real coefficients the universal coefficient theorem says that $$`H^k(M; \mathbb{R}) \cong \operatorname{Hom}(H_k(M), \mathbb{R}) = \left( H_k(M) \right)^\vee`
where we view $`H_k(X)` as a real vector space.

Consider the cochain complex $$`0 \to \Omega^0(M) \xrightarrow{d} \Omega^1(M) \xrightarrow{d} \Omega^2(M) \xrightarrow{d} \Omega^3(M) \xrightarrow{d} \dots`
and let $`H_{\mathrm{dR}}^k(M)` denote its cohomology groups.
Thus the de Rham cohomology is the closed forms modulo the exact forms.

The whole punch line is:

:::THEOREM "de Rham's theorem"
For any smooth manifold $`M`, we have a natural isomorphism $$`H^k(M; \mathbb{R}) \cong H_{\mathrm{dR}}^k(M).`
:::

So the theorem is that the real cohomology groups of manifolds $`M` are actually just given by the behavior of differential forms.
Thus,

:::MORAL
One can metaphorically think of elements of cohomology groups as $`G`-valued differential forms on the space.
:::

Why does this happen?
In fact, we observed already behavior of differential forms which reflects holes in the space.
For example, let $`M = S^1` be a circle and consider the *angle form* $`\alpha`.
The form $`\alpha` is closed, but not exact, because it is possible to run a full circle around $`S^1`.
So the failure of $`\alpha` to be exact is signaling that $`H_1(S^1) \cong \mathbb{Z}`.

As another piece of intuition, note that each $`k`-differential form $`\omega` can be interpreted as a function that takes each $`k`-smooth submanifold $`S \subseteq M`, and returns a real number $`\int_S \omega`.
Comparing with the description of cochains, cocycles, and coboundaries, we see the differential forms are a nicer subclass satisfying linearity and smoothness properties; and both the numerator and denominator get bigger in a way that _cancels out_: $$`H^k(M; \mathbb{R}) = \frac{\text{cocycles}}{\text{coboundaries}} \cong \frac{\text{cocycles} \cap \text{forms}}{\text{coboundaries} \cap \text{forms}} = H_{\mathrm{dR}}^k(M).`

Or, as a figure (for space reasons, the group of differential forms is denoted $`D`):

:::figure "figures/homology/cupproduct-second-iso.svg"
The forms $`D` and the cocycles share a "second isomorphism theorem" configuration, so the two quotients agree.
:::

# Graded rings

:::PROTOTYPE
Polynomial rings are commutative graded rings, while $`\bigwedge^\bullet(V)` is anticommutative.
:::

In the de Rham cohomology, the differential forms can interact in another way: given a $`k`-form $`\alpha` and an $`\ell`-form $`\beta`, we can consider a $`(k+\ell)`-form $`\alpha \wedge \beta`.
So we can equip the set of forms with a "product", satisfying $`\beta \wedge \alpha = (-1)^{k\ell} \alpha \wedge \beta`.
This is a special case of a more general structure:

:::DEFINITION
A *graded pseudo-ring* $`R` is an abelian group $$`R = \bigoplus_{d \ge 0} R^d`
where $`R^0`, $`R^1`, …, are abelian groups, with an additional associative binary operation $`\times \colon R \to R`.
We require that if $`r \in R^d` and $`s \in R^e`, we have $`rs \in R^{d+e}`.
Elements of an $`R^d` are called *homogeneous elements*; if $`r \in R^d` and $`r \neq 0`, we write $`|r| = d`.
:::

Note that we do _not_ assume commutativity.
In fact, these "rings" may not even have an identity $`1`.

:::DEFINITION
A *graded ring* is a graded pseudo-ring with $`1`.
If it is commutative we say it is a *commutative graded ring*.
:::

:::DEFINITION
A graded (pseudo-)ring $`R` is *anticommutative* if for any homogeneous $`r` and $`s` we have $$`rs = (-1)^{|r| |s|} sr.`
:::

:::EXAMPLE "Examples of graded rings"
1. The ring $`R = \mathbb{Z}[x]` is a *commutative graded ring*, with the $`d`th component being the multiples of $`x^d`.
2. The ring $`R = \mathbb{Z}[x, y, z]` is a *commutative graded ring*, with the $`d`th component being the abelian group of homogeneous degree $`d` polynomials (and $`0`).
3. Let $`V` be a vector space, and consider the abelian group $`\bigwedge^\bullet(V) = \bigoplus_{d \ge 0} \bigwedge^d(V)`.
   We endow $`\bigwedge^\bullet(V)` with the product $`\wedge`, which makes it into an *anticommutative ring*.
4. Consider the set of differential forms of a manifold $`M`, say $`\Omega^\bullet(M) = \bigoplus_{d \ge 0} \Omega^d(M)` endowed with the product $`\wedge`.
   This is an *anticommutative ring*.

All four examples have a multiplicative identity.
:::

:::aside
Mathlib formalizes graded rings as {name}`GradedRing`, a decomposition $`R = \bigoplus_i R_i` compatible with the multiplication; graded-commutative algebras and the exterior algebra $`\bigwedge^\bullet(V)` of example (c) are instances, the latter as {name}`ExteriorAlgebra` with its $`\mathbb{N}`-grading.

```lean
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Type _ := ExteriorAlgebra R M
```

The cohomology ring, cup product, Poincaré duality, and Künneth formula of this chapter are topological constructions that Mathlib does not yet carry, so they are presented here mathematically.
:::

Returning to $`\Omega^\bullet(M)`, we claim that the wedge product induces a map $`\wedge \colon H_{\mathrm{dR}}^k(M) \times H_{\mathrm{dR}}^\ell(M) \to H_{\mathrm{dR}}^{k+\ell}(M)`, using the Leibniz identity $`d(\alpha \wedge \beta) = (d\alpha) \wedge \beta + (-1)^{|\alpha|}\alpha \wedge (d\beta)` to check that the product of closed forms is closed and the product with an exact form is exact.
Therefore, we can obtain an *anticommutative ring* $`H_{\mathrm{dR}}^\bullet(M) = \bigoplus_{k \ge 0} H_{\mathrm{dR}}^k(M)` with $`\wedge` as a product.

# Cup products

Inspired by this, we want to see if we can construct a similar product on $`\bigoplus_{k \ge 0} H^k(X; R)` for any topological space $`X` and ring $`R`.
The way to do this is via the _cup product_.

:::DEFINITION
Suppose $`\phi \in C^k(X; R)` and $`\psi \in C^\ell(X; R)`.
Then we can define their *cup product* $`\phi \smile \psi \in C^{k+\ell}(X; R)` to be $$`(\phi \smile \psi)([v_0, \dots, v_{k+\ell}]) = \phi\left( [v_0, \dots, v_k] \right) \cdot \psi\left( [v_k, \dots, v_{k+\ell}] \right)`
where the multiplication is in $`R`.
:::

:::QUESTION
Assuming $`R` has a $`1`, which $`0`-cochain is the identity for $`\smile`?
:::

::::REMARK "Warning"
While you can interpret a $`n`-differential form as a $`n`-cochain the obvious way, the cup product is _not_ directly a generalization of the wedge product!
For example, let $`X = \mathbb{R}^2`, and try to evaluate $`dx \smile dy` on $`[v_0, v_1, v_2]` and $`[v_2, v_1, v_0]` where $`v_0 = (1, 0)`, $`v_1 = (0, 0)`, $`v_2 = (0, 1)`, assume all of the edges are straight lines.

This is because we are not having the alternation operator.
Refer to the discussion of the wedge product as a dual in the differential forms chapter for details.
In this case, the ring $`G` might be $`\mathbb{Z}` where not all nonzero elements have an inverse, so division would cause trouble.

Nevertheless, the differences will nicely cancel out, and we still have the corresponding element in the cohomology group equal to the element interpreted by the wedge product $`dx \wedge dy` — this is what we mean by $`H^\bullet(M; \mathbb{R}) \cong H_{\mathrm{dR}}^\bullet(M)`, stated below.

Let us consider the familiar example of a torus, and the $`1`-cocycles "$`dx`" and "$`dy`".

:::figure "figures/homology/cupproduct-torus-dxdy.svg"
The $`1`-cocycles "$`dx`" and "$`dy`" on the torus, with their values on some marked $`1`-chains.
:::

From what we know about the wedge product, we want $`(dx \wedge dy)(T) = 1` for $`T` the whole torus (up to a $`\pm` sign).
Indeed, with the definition above (work it out! Divide $`T` into two triangles arbitrarily) it will work.

Nevertheless, we don't really care about the cup product itself as much as the induced cup product on the homology ring.
::::

First, we prove an analogous result as before:

:::LEMMA "$\\delta$ with cup products"
We have $`\delta(\phi \smile \psi) = \delta\phi \smile \psi + (-1)^k \phi \smile \delta\psi`.
:::

Thus, by the same routine we used for de Rham cohomology, we get an induced map $`\smile \colon H^k(X; R) \times H^\ell(X; R) \to H^{k+\ell}(X; R)`.
We then define the *singular cohomology ring* whose elements are finite sums in $`H^\bullet(X; R) = \bigoplus_{k \ge 0} H^k(X; R)` and with multiplication given by $`\smile`.
Thus it is a graded ring (with $`1_R \in R` the identity) and is in fact anticommutative:

:::PROPOSITION "Cohomology is anticommutative"
$`H^\bullet(X; R)` is an anticommutative ring, meaning $`\phi \smile \psi = (-1)^{k\ell} \psi \smile \phi`.
:::

Moreover, we have the de Rham isomorphism:

:::THEOREM "de Rham extends to ring isomorphism"
For any smooth manifold $`M`, the isomorphism of de Rham cohomology groups to singular cohomology groups in fact gives an isomorphism $$`H^\bullet(M; \mathbb{R}) \cong H_{\mathrm{dR}}^\bullet(M)`
of anticommutative rings.
:::

We now present (mostly without proof) the cohomology rings of some common spaces.

:::EXAMPLE "Cohomology of torus"
The cohomology ring $`H^\bullet(S^1 \times S^1; \mathbb{Z})` of the torus is generated by elements $`|\alpha| = |\beta| = 1` which satisfy the relations $`\alpha \smile \alpha = \beta \smile \beta = 0`, and $`\alpha \smile \beta = -\beta \smile \alpha`.
Thus as a $`\mathbb{Z}`-module it is $$`H^\bullet(S^1 \times S^1; \mathbb{Z}) \cong \mathbb{Z} \oplus \left[ \alpha \mathbb{Z} \oplus \beta \mathbb{Z} \right] \oplus (\alpha \smile \beta) \mathbb{Z}.`
This gives the expected dimensions $`1 + 2 + 1 = 4`.
:::

:::EXAMPLE "Cohomology ring of $S^n$"
Consider $`S^n` for $`n \ge 1`.
As an abelian group $`H^\bullet(S^n; \mathbb{Z}) \cong \mathbb{Z} \oplus \alpha \mathbb{Z}` where $`\alpha` is the generator of $`H^n(S^n, \mathbb{Z})`.
Now, observe that $`|\alpha \smile \alpha| = 2n`, but since $`H^{2n}(S^n; \mathbb{Z}) = 0` we must have $`\alpha \smile \alpha = 0`.
So even more succinctly, $$`H^\bullet(S^n; \mathbb{Z}) \cong \mathbb{Z}[\alpha]/(\alpha^2).`
:::

:::EXAMPLE "Cohomology ring of real and complex projective space"
It turns out that $$`H^\bullet(\mathbb{RP}^n; \mathbb{Z}/2) \cong \mathbb{Z}/2[\alpha]/(\alpha^{n+1}), \qquad H^\bullet(\mathbb{CP}^n; \mathbb{Z}) \cong \mathbb{Z}[\beta]/(\beta^{n+1})`
where $`|\alpha| = 1` is a generator of $`H^1(\mathbb{RP}^n; \mathbb{Z}/2)` and $`|\beta| = 2` is a generator of $`H^2(\mathbb{CP}^n; \mathbb{Z})`.
:::

Already we have an interesting example where the cup product $`\smile` is different from the wedge product $`\wedge` — if $`n \geq 2`, then the generators $`\alpha` and $`\beta` above have $`\alpha \smile \alpha \neq 0` and $`\beta \smile \beta \neq 0`.

Let us try to see what happens here.
The formula above says $$`H^\bullet(\mathbb{RP}^2; \mathbb{Z}/2) \cong \mathbb{Z}/2[\alpha]/(\alpha^3).`
As an abelian group, there is a single nonzero element in $`H^0(\mathbb{RP}^2; \mathbb{Z}/2)`, $`H^1(\mathbb{RP}^2; \mathbb{Z}/2)`, and $`H^2(\mathbb{RP}^2; \mathbb{Z}/2)`, and the remaining groups are $`0`.

$`\mathbb{RP}^2` isn't too hard to visualize — it's just a $`2`-sphere, quotient by the relation to identify opposite vertices.

There is a $`1`-cycle on it that is not homologous to $`0`:

:::figure "figures/homology/cup-product-1cycle.svg"
:::

It's not very easy to show, but every such $`1`-cycle is homologous to each other, and double of that cycle is homologous to $`0`.

As such, $`H^1(\mathbb{RP}^2; \mathbb{Z}/2) \cong \operatorname{Hom}(H_1(\mathbb{RP}^2), \mathbb{Z}/2)`, its only nontrivial element $`\alpha` maps each such $`1`-cycle to $`1`.

# Relative cohomology pseudo-rings

For $`A \subseteq X`, one can also define a relative cup product $$`H^k(X, A; R) \times H^\ell(X, A; R) \to H^{k+\ell}(X, A; R).`
After all, if either cochain vanishes on chains in $`A`, then so does their cup product.
This lets us define *relative cohomology pseudo-ring* and *reduced cohomology pseudo-ring* (by $`A = \{\ast\}`), say $$`H^\bullet(X, A; R) = \bigoplus_{k \ge 0} H^k(X, A; R), \qquad \widetilde H^\bullet(X; R) = \bigoplus_{k \ge 0} \widetilde H^k(X; R).`
These are both *anticommutative pseudo-rings*.
Indeed, often we have $`\widetilde H^0(X; R) = 0` and thus there is no identity at all.

Once again we have functoriality:

:::THEOREM "Cohomology (pseudo-)rings are functorial"
Fix a ring $`R` (commutative with $`1`).
Then we have functors $$`H^\bullet(-; R) \colon \mathbf{hTop}^{\operatorname{op}} \to \mathbf{GradedRings}, \qquad H^\bullet(-, -; R) \colon \mathbf{hPairTop}^{\operatorname{op}} \to \mathbf{GradedPseudoRings}.`
:::

Unfortunately, unlike with (co)homology groups, it is a nontrivial task to determine the cup product for even nice spaces like CW complexes.{margin}[Apart from the method of passing to differential forms and back, that is. You have already computed a wedge product above.]
So we will not do much in the way of computation.
However, there is a little progress we can make.

# Wedge sums

Our goal is to now compute $`\widetilde H^\bullet(X \vee Y)`.
To do this, we need to define the product of two graded pseudo-rings:

:::DEFINITION
Let $`R` and $`S` be two graded pseudo-rings.
The *product pseudo-ring* $`R \times S` is the graded pseudo-ring defined by taking the underlying abelian group as $$`R \oplus S = \bigoplus_{d \ge 0} (R^d \oplus S^d).`
Multiplication comes from $`R` and $`S`, followed by declaring $`r \cdot s = 0` for $`r \in R`, $`s \in S`.
:::

Note that this is just graded version of the product ring defined earlier.

:::EXERCISE
Show that if $`R` and $`S` are graded rings (meaning they have $`1_R` and $`1_S`), then so is $`R \times S`.
:::

Now, the theorem is that:

:::THEOREM "Cohomology pseudo-rings of wedge sums"
We have $$`\widetilde H^\bullet(X \vee Y; R) \cong \widetilde H^\bullet(X; R) \times \widetilde H^\bullet(Y; R)`
as graded pseudo-rings.
:::

Knowing just that the rings are isomorphic doesn't help much, it would be much better if you know what the isomorphism is — so that in simple cases, you can see for yourself the rings are isomorphic.

The isomorphism is the most trivial one: given $`f \in C^\bullet(X \vee Y; R)` that assigns to each chain $`c` inside $`X \vee Y` a value $`f(c) \in R`, we can interpret it as an element of $`C^\bullet(X)`, because each chain inside $`X` is trivially a chain inside $`X \vee Y` that can be fed into $`f` — formally, the embedding $`X \hookrightarrow X \vee Y` induces $`C_\bullet(X) \hookrightarrow C_\bullet(X \vee Y)`.
The map induces a $`\widetilde H^\bullet(X \vee Y; R) \to \widetilde H^\bullet(X; R) \times \widetilde H^\bullet(Y; R)`, and it respects the ring multiplication i.e. the cup product.

::::EXAMPLE "A wedge of a square and a circle"
Let $`X` be a square and $`Y` a circle, so that $`X \vee Y` is the two fused at a point.

:::figure "figures/homology/cupproduct-wedge.svg"
The wedge $`X \vee Y` of a square and a circle, joined at a single point.
:::
Let $`f \in \widetilde H^1(X; \mathbb{Z})` assign $`f(X) = 2` to the whole square, and $`g \in \widetilde H^1(Y; \mathbb{Z})` assign $`g(Y) = 3` to the whole circle.
Then, of course the element corresponding to $`(f, g)` inside $`\widetilde H^1(X \vee Y)` would assign $`2 + 3 = 5` to the cocycle corresponding to the whole space $`X \vee Y`.
::::

This allows us to resolve the first question posed at the beginning.
Let $`X = \mathbb{CP}^2` and $`Y = S^2 \vee S^4`.
We have that $$`H^\bullet(\mathbb{CP}^2; \mathbb{Z}) \cong \mathbb{Z}[\alpha] / (\alpha^3).`
Hence this is a graded ring generated by three elements:

- $`1`, in dimension $`0`.
- $`\alpha`, in dimension $`2`.
- $`\alpha^2`, in dimension $`4`.

Next, consider the reduced cohomology pseudo-ring $$`\widetilde H^\bullet(S^2 \vee S^4; \mathbb{Z}) \cong \widetilde H^\bullet(S^2; \mathbb{Z}) \oplus \widetilde H^\bullet(S^4; \mathbb{Z}).`
Thus the absolute cohomology ring $`H^\bullet(S^2 \vee S^4; \mathbb{Z})` is a graded ring also generated by three elements.

- $`1`, in dimension $`0` (once we add back in the $`0`th dimension).
- $`a_2`, in dimension $`2` (from $`H^\bullet(S^2; \mathbb{Z})`).
- $`a_4`, in dimension $`4` (from $`H^\bullet(S^4; \mathbb{Z})`).

Each graded component is isomorphic, like we expected.
However, in the former, the product of two degree $`2` generators is $$`\alpha \cdot \alpha = \alpha^2.`
In the latter, the product of two degree $`2` generators is $$`a_2 \cdot a_2 = a_2^2 = 0`
since $`a_2 \smile a_2 = 0 \in H^\bullet(S^2; \mathbb{Z})`.

Thus $`S^2 \vee S^4` and $`\mathbb{CP}^2` are not homotopy equivalent.

Intuitively, what the proof above says is:

:::MORAL
The nontrivial $`4`-cocycle $`a_4 \in H^4(S^2 \vee S^4; \mathbb{Z})` has nothing to do with the $`2`-cocycle $`a_2`, while the $`4`-cocycle $`\alpha^2 \in H^4(\mathbb{CP}^2)` is the cup product $`\alpha \smile \alpha` of the $`2`-cocycle $`\alpha` with itself.
:::

:::figure "figures/homology/cupproduct-rp2-cocycle.svg"
The projective plane $`\mathbb{RP}^2` as a square with both edge-pairs reversed: the nonzero $`\alpha \in H^1(\mathbb{RP}^2; \mathbb{Z}/2)` acts like both $`dx` and $`dy` at once, so $`\alpha \smile \alpha` assigns $`1` to the whole surface and is nonzero.
:::

The exercise below would be much easier to visualize, apart from the fact that $`\mathbb{RP}^2` is nonorientable — in fact, we have already seen above why $`\alpha \smile \alpha \neq 0` for the nonzero element $`\alpha \in H^1(\mathbb{RP}^2)`.

:::EXERCISE
Similarly, show that $`S^1 \vee S^2` and $`\mathbb{RP}^2` are not homotopy equivalent by showing $`\widetilde H^\bullet(S^1 \vee S^2; \mathbb{Z}/2) \not\cong \widetilde H^\bullet(\mathbb{RP}^2; \mathbb{Z}/2)`, even though each graded component is isomorphic.
:::

# Cross product

In this section, we will define the cross product.

## Motivation

Roughly speaking, the motivation is the following:

:::MORAL
If $`X` has a $`m`-dimensional hole and $`Y` has a $`n`-dimensional hole, then $`X \times Y` has a $`(m + n)`-dimensional hole.
:::

Which is true in most common cases under suitable interpretation of "holes" (either with homology, or with cohomology).

We will formalize and prove the statement above.

## Cross product on singular homology

First, we define the *cross product*, that takes a $`m`-simplex $`f \colon \Delta^m \to X` and a $`n`-simplex $`g \colon \Delta^n \to Y`, and returns a $`(m + n)`-chain $`f \times g \in C_{m + n}(X \times Y)`.{margin}[As far as I know, this is just because the symbol $`\times` is a cross, and it has nothing to do with the cross product of vectors in $`\mathbb{R}^3`.]
This is really the most natural way you might define it: intuitively, the product of a $`m`-dimensional cube in $`X` and a $`n`-dimensional cube in $`Y` is a $`(m + n)`-dimensional cube in $`X \times Y`.

:::figure "figures/homology/cupproduct-cross-product.svg"
A cube $`U` in $`X` and a cube $`V` in $`Y` give a product cube $`U \times V` in $`X \times Y`.
:::

In the case of a simplex, we need to subdivide $`\Delta^m \times \Delta^n` into finitely many copies of $`\Delta^{m + n}`.

If $`n = 1`, we have already seen a subdivision when we worked with the prism operator.
For the general case, refer to {cite}`ref:hatcher`, page 277 — the number blows up quickly, for example, you need $`\binom{30}{15} = 155117520` simplices to cover $`\Delta^{15} \times \Delta^{15}`!

Formally, we can define the cross product of chains: that is, a function $$`C_m(X) \times C_n(Y) \xrightarrow{\times} C_{m + n}(X \times Y).`
We can prove that this induces a map on homology groups: $$`H_m(X) \times H_n(Y) \xrightarrow{\times} H_{m + n}(X \times Y).`

:::EXERCISE
Let $`X = Y = S^1`, so that $`X \times Y` is a torus.
Let $`\alpha` be a generator of $`H_1(X)`, and $`\beta` be a generator of $`H_1(Y)`.
Show that $`\alpha \times \beta` is the generator of $`H_2(X \times Y)`.
:::

Actually, we have the following:

:::THEOREM "Cross product of nonzero classes is nonzero"
If $`X` and $`Y` are CW complexes and $`R` is a PID, then the cross product of two nonzero elements in $`H_m(X)` and $`H_n(Y)` is nonzero.
:::

Thus formalize our intuition earlier — at least, if we use homology as a measure of "holes".

## Cross product is not a ℤ-module homomorphism

For this section, if $`a` and $`b` are elements of the $`\mathbb{Z}`-module $`C_m(X)` and $`C_n(Y)` respectively, we write $`\times(a, b)` to mean $`a \times b \in C_{m + n}(X \times Y)`, and $`(a, b)` to be the element that corresponds in the product $`C_m(X) \times C_n(Y)`.

There is a little technical detail that we need to sort out — above, we write $$`\times \colon C_m(X) \times C_n(Y) \to C_{m + n}(X \times Y).`
But written this way, $`\times` is not a $`\mathbb{Z}`-module homomorphism!

:::EXAMPLE "The cross product is not linear on the product"
Let $`a` and $`b` be any nonzero elements in $`C_m(X)` and $`C_n(Y)` respectively.
Then, $$`\times(a, b) = a \times b, \qquad 2 \cdot (a, b) = (2a, 2b), \qquad \times(2 \cdot (a, b)) = 4(a \times b).`
:::

If we want to talk about isomorphism, or do anything with the $`\mathbb{Z}`-module structure of $`C_{m + n}(X \times Y)` or $`H_{m + n}(X \times Y)`, we'd better having a $`\mathbb{Z}`-module homomorphism.

This is easy enough to fix: $`\times` is bilinear, so it's natural to consider the tensor product: $$`\times \colon C_m(X) \otimes_{\mathbb{Z}} C_n(Y) \to C_{m + n}(X \times Y).`
With this notation, $`\times(a \otimes b) = a \times b`.
(As a side effect, we can also write $`\times(a \otimes b + c \otimes d) = a \times b + c \times d` now.)

And so, let us restate the theorem above:

:::THEOREM "Cross product on homology, tensor form"
If $`X` and $`Y` are CW complexes, then $$`\times \colon H_m(X) \otimes_{\mathbb{Z}} H_n(Y) \to H_{m + n}(X \times Y)`
is an injective $`\mathbb{Z}`-module homomorphism.
:::

## Cross product on cellular homology

The definition with singular homology is quite clumsy — because we use simplices as the building blocks for the chains, the product of two simplices in $`X` and $`Y` becomes a huge collection of simplices in $`X \times Y`.

We will now redefine the cross product using cellular homology — it can be safely skipped, since both definitions of the cross product gives identical result on the homology groups.

If $`X` and $`Y` are CW complexes, we can do better.
We see that $`X \times Y` has a natural CW complex structure: for each cell $`e^m` of $`X` and cell $`e^n` of $`Y`, their product makes for a cell $`e^{m + n}` of $`X \times Y`.

:::EXAMPLE "Product of two segments"
If $`X` and $`Y` are both line segments built from two $`0`-cells and one $`1`-cell, then their product $`X \times Y` has a natural CW complex structure containing:

- $`4` $`0`-cells,
- $`4` $`1`-cells,
- $`1` $`2`-cell.
:::

Recall the cellular groups $`\operatorname{Cells}_\bullet(X)` from the cellular homology chapter, each basis element corresponds to a cell in $`X`.
Then, we can define the cross product on the basis elements: $$`\times \colon \operatorname{Cells}_m(X) \otimes_{\mathbb{Z}} \operatorname{Cells}_n(Y) \to \operatorname{Cells}_{m + n}(X \times Y).`
To be painfully explicit: let $`e^m \in \operatorname{Cells}_m(X)`, $`e^n \in \operatorname{Cells}_n(Y)`, then the cross product is defined by $`e^m \times e^n = e^m \times e^n \in \operatorname{Cells}_{m + n}(X \times Y)` — even the notation used is trivial.

Of course, this induces a map on the homology groups: $$`\times \colon H_m(X) \otimes_{\mathbb{Z}} H_n(Y) \to H_{m + n}(X \times Y).`
This map is the same as the map we defined earlier.

## Cross product on cellular cohomology

We do the same thing as above, but this time with cohomology — remember that homology and cohomology are slightly different measures of "holes", for $`K` the Klein bottle then $`H_2(K) = 0` but $`H^2(K; \mathbb{Z}) \neq 0`.

Given two cellular cochains $`f \in \operatorname{Hom}(\operatorname{Cells}_m(X); R)` and $`g \in \operatorname{Hom}(\operatorname{Cells}_n(Y); R)`, we want to obtain a cochain $`f \times g \in \operatorname{Hom}(\operatorname{Cells}_{m + n}(X \times Y); R)`.

Of course, it is defined in the most natural way possible: for a cell $`e^m` of $`X` and a cell $`e^n` of $`Y`, we have $`(f \times g)(e^m \times e^n) = f(e^m) \cdot g(e^n)`.

Sounds good?
Not yet — since not all $`(m + n)`-cells $`e^{m + n}` of $`X \times Y` is formed as a product of a $`m`-cell in $`X` and a $`n`-cell in $`Y`.
For those, we simply declare that $`(f \times g)(e^{m + n}) = 0`.

As usual, this map induces a $`R`-module homomorphism on the cohomology groups: $$`\times \colon H^m(X; R) \otimes_R H^n(Y; R) \to H^{m + n}(X \times Y; R).`

## Motivation: cross product of differential forms

The definition of the cross product of two cellular cochains above are clean, but may appear to be dry and unmotivated.

Turns out you can do the same thing on differential forms.
What's more, it gives a clean way of defining the wedge product $`\alpha \wedge \beta`!
Let's see it in action.

Instead of the definition, here are a few examples.
Motivated readers may try to define the concept formally.

:::EXAMPLE "Examples of cross product of differential forms"
Here are a few examples.

- If $`X` and $`Y` are the $`x`-axis and the $`y`-axis of the plane respectively, the cross product $`dx \times 2\,dy` is equal to $`2(dx \wedge dy)`.

  Certainly this is natural — as $`dx` assigns the value $`1` to the vector $`e_1`, and $`2\,dy` assigns the value $`2` to the vector $`e_2`, we get that $`dx \times 2\,dy` should assign the value $`1 \cdot 2 = 2` to the unit square spanned by $`e_1` and $`e_2` — that is, $`e_1 \wedge e_2`.
- Let $`X` be the $`xy`-plane, and let $`Y` be the $`z`-axis.
  Consider the cross product $`dx \times dz`.
  What $`2`-form should the result be?

  Certainly, we should have $`(dx \times dz)(e_1 \wedge e_3) = 1` and $`(dx \times dz)(e_2 \wedge e_3) = 0`.
  But this isn't enough to uniquely determine $`dx \times dz`.

  And so, we declare: $`(dx \times dz)(e_1 \wedge e_2) = 0`.
  With this, we get $`dx \times dz = dx \wedge dz`.
:::

More generally, we can define the cross product by picking a basis for $`X` and $`Y`, and define the value of $`\alpha \times \beta` on the basis elements.

As promised — you can define the wedge product using the cross product.
There's only one thing you can do:

:::DEFINITION
For $`X` a $`\mathbb{R}`-vector space, let $`\alpha \in \left(\bigwedge^m(X)\right)^\vee` and $`\beta \in \left(\bigwedge^n(X)\right)^\vee`, then $`\alpha \wedge \beta \in \left(\bigwedge^{m + n}(X)\right)^\vee` is defined by $$`\alpha \wedge \beta = \Delta^\ast(\alpha \times \beta)`
where $`\Delta \colon X \to X \times X`, $`\Delta(x) = (x, x)` is the diagonal map.
Recall that $`\Delta^\ast` denotes the pullback operation.
:::

In simpler terms: to evaluate $`\alpha \wedge \beta` on a $`(m + n)`-wedge in $`X`, push it to $`X \times X` using the diagonal map, and give it to $`\alpha \times \beta`.

## Piecing the cohomology groups together

Recall that we have above the $`R`-module homomorphism $$`\times \colon H^m(X; R) \otimes_R H^n(Y; R) \to H^{m + n}(X \times Y; R).`
We know that it is in fact possible to piece all the $`H^\bullet(X; R)` together to form an anticommutative graded ring, the cohomology ring.
So we wish to extend the map to a $`R`-algebra homomorphism $$`\times \colon H^\bullet(X; R) \otimes_R H^\bullet(Y; R) \to H^\bullet(X \times Y; R).`

We haven't defined what the tensor product of two graded rings is yet — we will formally do that in the next section, but intuitively, it consists of all the $`H^m(X; R) \otimes_R H^n(Y; R)` pieced together.

# Künneth formula

We now wish to tell apart the spaces $`S^2 \times S^4` and $`\mathbb{CP}^3`.
In order to do this, we will need a formula for $`H^n(X \times Y; R)` in terms of $`H^n(X; R)` and $`H^n(Y; R)`.
These formulas are called *Künneth formulas*.
In this section we will only use a very special case, which involves the tensor product of two graded rings.

:::DEFINITION
Let $`A` and $`B` be two graded rings which are also $`R`-modules.
We define the *tensor product* $`A \otimes_R B` as follows.
As an abelian group, it is $$`A \otimes_R B = \bigoplus_{d \ge 0} \left( \bigoplus_{k=0}^{d} A^k \otimes_R B^{d-k} \right).`
The multiplication is given on basis elements by $`(a_1 \otimes b_1)(a_2 \otimes b_2) = (a_1 a_2) \otimes (b_1 b_2)`.
Of course the multiplicative identity is $`1_A \otimes 1_B`.
:::

Now let $`X` and $`Y` be topological spaces.

:::figure "figures/homology/cupproduct-projections.svg"
The product $`X \times Y` with its projections $`\pi_X`, $`\pi_Y` onto the two factors.
:::

Using the projections $`\pi_X`, $`\pi_Y` of $`X \times Y`, functoriality gives induced maps $`\pi_X^\ast` and $`\pi_Y^\ast`, and we define the *cross product* $$`H^\bullet(X; R) \otimes_R H^\bullet(Y; R) \xrightarrow{\times} H^\bullet(X \times Y; R)`
acting on cocycles by $`\phi \times \psi = \pi_X^\ast(\phi) \smile \pi_Y^\ast(\psi)`.

:::THEOREM "Künneth formula"
Let $`X` and $`Y` be CW complexes such that $`H^k(Y; R)` is a finitely generated free $`R`-module for every $`k`.
Then the cross product is an isomorphism of anticommutative rings $$`H^\bullet(X; R) \otimes_R H^\bullet(Y; R) \to H^\bullet(X \times Y; R).`
:::

That is:

:::MORAL
There is a one-to-one correspondence between pairs of holes in $`X` and $`Y` and holes of $`X \times Y`.
Furthermore, the correspondence respects the cup product.
:::

In any case, this finally lets us resolve the question set out at the beginning.
We saw that $`H_n(\mathbb{CP}^3) \cong H_n(S^2 \times S^4)` for every $`n`, and thus $`H^n(\mathbb{CP}^3; \mathbb{Z}) \cong H^n(S^2 \times S^4; \mathbb{Z})` too.

But now let us look at the cohomology rings.
First, $`H^\bullet(\mathbb{CP}^3; \mathbb{Z}) \cong \mathbb{Z}[\alpha]/(\alpha^4)` with $`|\alpha| = 2`, generated by $`1`, $`\alpha`, $`\alpha^2`, $`\alpha^3` in degrees $`0, 2, 4, 6`.
On the other hand $`H^\bullet(S^2 \times S^4; \mathbb{Z}) \cong \mathbb{Z}[\beta]/(\beta^2) \otimes \mathbb{Z}[\gamma]/(\gamma^2)`, generated by $`1 \otimes 1`, $`\beta \otimes 1`, $`1 \otimes \gamma`, $`\beta \otimes \gamma` in degrees $`0, 2, 4, 6`.
Again in each dimension we have the same abelian group.
But notice that if we square $`\beta \otimes 1` we get $`(\beta \otimes 1)(\beta \otimes 1) = \beta^2 \otimes 1 = 0`, yet the degree $`2` generator of $`H^\bullet(\mathbb{CP}^3; \mathbb{Z})` does not have this property.
Hence these two graded rings are not isomorphic.

So it follows that $`\mathbb{CP}^3` and $`S^2 \times S^4` are not homotopy equivalent.

:::MORAL
The nontrivial $`4`-cocycle $`1 \otimes \gamma` of $`S^2 \times S^4` is orthogonal to the $`2`-cocycle $`\beta \otimes 1`, while the $`4`-cocycle $`\alpha^2` of $`\mathbb{CP}^3` is the cup product $`\alpha \smile \alpha` of the $`2`-cocycle $`\alpha` with itself.
:::

# Problems

:::PROBLEM "Symmetry of Betti numbers by Poincaré duality"
Let $`M` be a smooth oriented compact $`n`-manifold, and let $`b_k` denote its Betti number.
Prove that $`b_k = b_{n-k}`.
(Hint: write $`H^k(M; \mathbb{Z})` in terms of $`H_k(M)` using the universal coefficient theorem, and analyze the ranks.)
:::

:::PROBLEM "Non-orientability of even projective space"
Show that $`\mathbb{RP}^n` is not orientable for even $`n`.
(Hint: use the previous result on Betti numbers.)
:::

:::PROBLEM "Distinguishing $\\mathbb{RP}^3$"
Show that $`\mathbb{RP}^3` is not homotopy equivalent to $`\mathbb{RP}^2 \vee S^3`.
(Hint: use the $`\mathbb{Z}/2` cohomologies, and find the cup product.)
:::

:::PROBLEM "Wedge is not a retract of product"
Show that $`S^m \vee S^n` is not a deformation retract of $`S^m \times S^n` for any $`m, n \ge 1`.
(Hint: assume that $`r \colon S^m \times S^n \to S^m \vee S^n` is such a map.
Show that the induced map $`H^\bullet(S^m \vee S^n; \mathbb{Z}) \to H^\bullet(S^m \times S^n; \mathbb{Z})` between their cohomology rings is monic.)
:::
