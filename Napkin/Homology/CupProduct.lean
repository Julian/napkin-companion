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

:::REMARK "Warning"
While you can interpret a $`n`-differential form as a $`n`-cochain the obvious way, the cup product is _not_ directly a generalization of the wedge product!
This is because we are not applying the alternation operator.
Nevertheless, the differences nicely cancel out, and the corresponding element in the cohomology group equals the element interpreted by the wedge product — this is what we mean by $`H^\bullet(M; \mathbb{R}) \cong H_{\mathrm{dR}}^\bullet(M)`.
:::

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
