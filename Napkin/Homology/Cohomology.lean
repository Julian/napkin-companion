import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open CategoryTheory

set_option pp.rawOnError true

#doc (Manual) "Singular cohomology" =>

%%%
file := "Singular-cohomology"
%%%

Here's one way to motivate this chapter.
It turns out that:

- $`H_n(\mathbb{CP}^2) \cong H_n(S^2 \vee S^4)` for every $`n`.
- $`H_n(\mathbb{CP}^3) \cong H_n(S^2 \times S^4)` for every $`n`.

This is unfortunate, because if possible we would like to be able to tell these spaces apart (as they are in fact not homotopy equivalent), but the homology groups cannot tell the difference between them.

In this chapter, we'll define a _cohomology group_ $`H^n(X)` and $`H^n(Y)`.
In fact, the $`H^n`'s are completely determined by the $`H_n`'s by the so-called _universal coefficient theorem_.
However, it turns out that one can take all the cohomology groups and put them together to form a _cohomology ring_ $`H^\bullet`.
We will then see that $`H^\bullet(X) \not\cong H^\bullet(Y)` as rings.

# Cochain complexes

:::DEFINITION
A *cochain complex* $`A^\bullet` is algebraically the same as a chain complex, except that the indices increase.
So it is a sequence of abelian groups $$`\dots \xrightarrow{\delta} A^{n-1} \xrightarrow{\delta} A^n \xrightarrow{\delta} A^{n+1} \xrightarrow{\delta} \dots.`
such that $`\delta^2 = 0`.
Notation-wise, we're now using superscripts, and use $`\delta` rather $`\partial`.
We define the *cohomology groups* by $$`H^n(A^\bullet) = \ker\left( A^n \xrightarrow{\delta} A^{n+1} \right) / \operatorname{img}\left( A^{n-1} \xrightarrow{\delta} A^n \right).`
:::

:::aside
In Mathlib this is {name}`CochainComplex`, the special case of {name}`HomologicalComplex` whose differential _raises_ the degree by one — the mirror image of {name}`ChainComplex`.
Its cohomology is computed by the very same {name}`HomologicalComplex.homology`.

```lean
example {V : Type*} [Category V] [Limits.HasZeroMorphisms V] :
    Type _ := CochainComplex V ℕ
```
:::

:::EXAMPLE "de Rham cohomology"
We have already met one example of a cochain complex: let $`M` be a smooth manifold and $`\Omega^k(M)` be the additive group of $`k`-forms on $`M`.
Then we have a cochain complex $$`0 \xrightarrow{d} \Omega^0(M) \xrightarrow{d} \Omega^1(M) \xrightarrow{d} \Omega^2(M) \xrightarrow{d} \dots.`
The resulting cohomology is called *de Rham cohomology*, described later.
:::

Aside from de Rham's cochain complex, *the most common way to get a cochain complex is to dualize a chain complex.*
Specifically, pick an abelian group $`G`; note that $`\operatorname{Hom}(-, G)` is a contravariant functor, and thus takes every chain complex into a cochain complex: letting $`A^n = \operatorname{Hom}(A_n, G)` we obtain a cochain complex where $`\delta(A_n \xrightarrow{f} G) = A_{n+1} \xrightarrow{\partial} A_n \xrightarrow{f} G`.

These are the cohomology groups we study most in algebraic topology, so we give a special notation to them.

:::DEFINITION
Given a chain complex $`A_\bullet` of abelian groups and another group $`G`, we let $`H^n(A_\bullet; G)` denote the cohomology groups of the dual cochain complex $`A^\bullet` obtained by applying $`\operatorname{Hom}(-, G)`.
In other words, $`H^n(A_\bullet; G) = H^n(A^\bullet)`.
:::

# Cohomology of spaces

:::PROTOTYPE
$`C^0(X; G)` all functions $`X \to G` while $`H^0(X)` are those functions $`X \to G` constant on path components.
:::

The case of interest is our usual geometric situation, with $`C_\bullet(X)`.

:::DEFINITION
For a space $`X` and abelian group $`G`, we define $`C^\bullet(X; G)` to be the dual to the singular chain complex $`C_\bullet(X)`, called the *singular cochain complex* of $`X`; its elements are called *cochains*.

Then we define the *cohomology groups* of the space $`X` as $$`H^n(X; G) \coloneqq H^n(C_\bullet(X); G) = H^n(C^\bullet(X; G)).`
:::

:::REMARK
Note that if $`G` is also a ring (like $`\mathbb{Z}` or $`\mathbb{R}`), then $`H^n(X; G)` is not only an abelian group but actually a $`G`-module.
:::

:::EXAMPLE "$C^0(X; G)$, $C^1(X; G)$, and $H^0(X; G)$"
Let $`X` be a topological space and consider $`C^\bullet(X)`.

- $`C_0(X)` is the free abelian group on $`X`, and $`C^0(X) = \operatorname{Hom}(C_0(X), G)`.
  So a $`0`-cochain is a function that takes every point of $`X` to an element of $`G`.
- $`C_1(X)` is the free abelian group on $`1`-simplices in $`X`.
  So $`C^1(X)` needs to take every $`1`-simplex to an element of $`G`.

Let's now try to understand $`\delta \colon C^0(X) \to C^1(X)`.
Given a $`0`-cochain $`\phi \in C^0(X)`, what is $`\delta\phi`?
Answer: $$`\delta\phi \colon [v_0, v_1] \mapsto \phi([v_0]) - \phi([v_1]).`
Hence, elements of $`\ker(C^0 \xrightarrow{\delta} C^1) \cong H^0(X; G)` are those cochains that are _constant on path-connected components_.
:::

In particular, much like $`H_0(X)`, we have $`H^0(X) \cong G^{\oplus r}` if $`X` has $`r` path-connected components (where $`r` is finite).{margin}[Something funny happens if $`X` has _infinitely_ many path-connected components: for homology we get a _direct sum_ $`\bigoplus_\alpha G` while for cohomology we get a _direct product_ $`\prod_\alpha G`. These are actually different for infinite indexing sets.]

:::ABUSE
In this chapter the only cochain complexes we will consider are dual complexes as above.
So, any time we write a cochain complex $`A^\bullet` it is implicitly given by applying $`\operatorname{Hom}(-, G)` to $`A_\bullet`.
:::

The higher cohomology groups $`H^n(X; G)` (or even the cochain groups $`C^n(X; G) = \operatorname{Hom}(C_n(X), G)`) are harder to describe concretely.

# Cohomology of spaces is functorial

We now check that the cohomology groups still exhibit the same nice functorial behavior.

:::EXERCISE
Interpret $`\operatorname{Hom}(-, G)` as a contravariant functor from $`\mathbf{Cmplx}^{\mathrm{op}} \to \mathbf{CoCmplx}`.
This means in particular that given a chain map $`f \colon A_\bullet \to B_\bullet`, we naturally obtain a dual map $`f^\vee \colon B^\bullet \to A^\bullet`.
:::

Then in exact analog to our result that $`H_n \colon \mathbf{hTop} \to \mathbf{Grp}` we have:

:::THEOREM "$H^n(-; G) \\colon \\mathbf{hTop}^{op} \\to \\mathbf{Grp}$"
For every $`n`, $`H^n(-; G)` is a contravariant functor from $`\mathbf{hTop}^{\mathrm{op}}` to $`\mathbf{Grp}`.
:::

:::PROOF
The idea is to leverage the work we already did in constructing the prism operator earlier.
So as before all we have to show is that if $`f \simeq g`, then $`f^\ast = g^\ast`.
Recall now that there is a prism operator such that $`f_\sharp - g_\sharp = P \partial + \partial P`.
If we apply the entire functor $`\operatorname{Hom}(-; G)` we get that $`f^\sharp - g^\sharp = \delta P^\vee + P^\vee \delta` where $`P^\vee \colon C^{n+1}(Y; G) \to C^n(X; G)`.
So $`f^\sharp` and $`g^\sharp` are chain homotopic thus $`f^\ast = g^\ast`.
:::

# Universal coefficient theorem

We now wish to show that the cohomology groups are determined up to isomorphism by the homology groups: given $`H_n(A_\bullet)`, we can extract $`H^n(A_\bullet; G)`.
This is achieved by the _universal coefficient theorem_.

:::THEOREM "Universal coefficient theorem"
Let $`A_\bullet` be a chain complex of _free_ abelian groups, and let $`G` be another abelian group.
Then there is a natural short exact sequence $$`0 \to \operatorname{Ext}(H_{n-1}(A_\bullet), G) \to H^n(A_\bullet; G) \xrightarrow{h} \operatorname{Hom}(H_n(A_\bullet), G) \to 0.`
In addition, this exact sequence is _split_ so in particular $$`H^n(C_\bullet; G) \cong \operatorname{Ext}(H_{n-1}(A_\bullet), G) \oplus \operatorname{Hom}(H_n(A_\bullet), G).`
:::

Fortunately, in our case of interest, $`A_\bullet` is $`C_\bullet(X)` which is by definition free.

It's not too hard to guess how $`h \colon H^n(A_\bullet; G) \to \operatorname{Hom}(H_n(A_\bullet), G)` is defined.
An element of $`H^n(A_\bullet; G)` is represented by a function which sends a cycle in $`A_n` to an element of $`G`.
The content of the theorem is to show that $`h` is surjective with kernel $`\operatorname{Ext}(H_{n-1}(A_\bullet), G)`.

What about $`\operatorname{Ext}`?
It turns out that $`\operatorname{Ext}(-, G)` is the so-called *Ext functor*, defined as follows.
Let $`H` be an abelian group, and consider a *free resolution* of $`H`, by which we mean an exact sequence $$`\dots \xrightarrow{f_2} F_1 \xrightarrow{f_1} F_0 \xrightarrow{f_0} H \to 0`
with each $`F_i` free.
Then we can apply $`\operatorname{Hom}(-, G)` to get a cochain complex which _need not be exact_, and we define $`\operatorname{Ext}(H, G) \coloneqq \ker(f_2^\vee) / \operatorname{img}(f_1^\vee)`; it's a theorem that this doesn't depend on the choice of the free resolution.

:::aside
Mathlib does have $`\operatorname{Ext}` groups (in `Mathlib.Algebra.Homology.DerivedCategory.Ext`), but they are set up in the general derived-category framework rather than the one-step free-resolution recipe used here, and the universal coefficient theorem itself is not part of the library.
So the $`\operatorname{Ext}` computations of this chapter are carried out concretely by choosing free resolutions.
:::

:::LEMMA "Computing the $\\operatorname{Ext}$ functor"
For any abelian groups $`G`, $`H`, $`H'` we have

1. $`\operatorname{Ext}(H \oplus H', G) = \operatorname{Ext}(H, G) \oplus \operatorname{Ext}(H', G)`.
2. $`\operatorname{Ext}(H, G) = 0` for $`H` free, and
3. $`\operatorname{Ext}(\mathbb{Z}/n, G) = G / nG`.
:::

:::PROOF
For (a), note that a direct sum of free resolutions is a free resolution.
For (b), note that $`0 \to H \to H \to 0` is a free resolution.
Part (c) follows by taking the free resolution $`0 \to \mathbb{Z} \xrightarrow{\times n} \mathbb{Z} \to \mathbb{Z}/n \to 0` and applying $`\operatorname{Hom}(-, G)` to it.
:::

:::QUESTION
Some $`\operatorname{Ext}` practice: compute $`\operatorname{Ext}(\mathbb{Z}^{\oplus 2015}, G)` and $`\operatorname{Ext}(\mathbb{Z}/30, \mathbb{Z}/4)`.
:::

# Example computation of cohomology groups

:::PROTOTYPE
Possibly $`H^n(S^m)`.
:::

The universal coefficient theorem gives us a direct way to compute any cohomology groups, provided we know the homology ones.

:::EXAMPLE "Cohomology groups of $S^m$"
It is straightforward to compute $`H^n(S^m)` now: all the $`\operatorname{Ext}` terms vanish since $`H_n(S^m)` is always free, and hence we obtain that $$`H^n(S^m) \cong \operatorname{Hom}(H_n(S^m), G) \cong \begin{cases} G & n = m, n = 0 \\ 0 & \text{otherwise}. \end{cases}`
:::

:::EXAMPLE "Cohomology groups of torus"
This example has no nonzero $`\operatorname{Ext}` terms either, since this time $`H_n(S^1 \times S^1)` is always free.
So we obtain $`H^n(S^1 \times S^1) \cong \operatorname{Hom}(H_n(S^1 \times S^1), G)`, giving $$`H^n(S^1 \times S^1) \cong \begin{cases} G & n = 0, 2 \\ G^{\oplus 2} & n = 1. \end{cases}`
:::

From these examples one might notice that:

:::LEMMA "$0$th and $1$st cohomology groups are just duals"
For $`n = 0` and $`n = 1`, we have $`H^n(X; G) \cong \operatorname{Hom}(H_n(X), G)`.
:::

:::PROOF
It's already been shown for $`n = 0`.
For $`n = 1`, notice that $`H_0(X)` is free, so the $`\operatorname{Ext}` term vanishes.
:::

:::EXAMPLE "Cohomology groups of Klein bottle"
This example will actually have $`\operatorname{Ext}` term.
Recall that if $`K` is a Klein Bottle then its homology groups are $`\mathbb{Z}` in dimension $`n = 0` and $`\mathbb{Z} \oplus \mathbb{Z}/2` in $`n = 1`, and $`0` elsewhere.

For $`n = 0`, we again just have $`H^0(K; G) \cong \operatorname{Hom}(\mathbb{Z}, G) \cong G`.
For $`n = 1`, the $`\operatorname{Ext}` term is $`\operatorname{Ext}(H_0(K), G) \cong \operatorname{Ext}(\mathbb{Z}, G) = 0` so $`H^1(K; G) \cong \operatorname{Hom}(\mathbb{Z} \oplus \mathbb{Z}/2, G) \cong G \oplus \operatorname{Hom}(\mathbb{Z}/2, G)`.
But for $`n = 2`, we have our first interesting $`\operatorname{Ext}` group, giving $`H^2(K; G) \cong \operatorname{Ext}(\mathbb{Z}/2, G) \cong G/2G`.
In summary: $$`H^n(K; G) \cong \begin{cases} G & n = 0 \\ G \oplus \operatorname{Hom}(\mathbb{Z}/2, G) & n = 1 \\ G/2G & n = 2 \\ 0 & n \ge 3. \end{cases}`
:::

# Interpreting the universal coefficient theorem

There are two key points to be read from the theorem:

- Even though $`H_n(A_\bullet) = 0`, it is still possible for $`H^n(A_\bullet; G) \neq 0` if $`\operatorname{Ext}(H_{n-1}(A_\bullet), G) \neq 0`.
- $`H^n(A_\bullet; G)` is uniquely determined by $`H_n(A_\bullet)` and $`G`, regardless of what $`A_\bullet` is, as long as each $`A_n` is free.

Which means: if you wish, you can forget about the formula in the universal coefficient theorem, and use the cellular chain complex $`\operatorname{Cells}_\bullet(X)` to compute cohomology by dualizing it.
After all, the cellular chain complex and the singular chain complex are both free and have the same homology groups, so by the universal coefficient theorem they must have the same cohomology groups.

Geometrically, a cocycle modulo coboundary can be "evaluated" on a cycle modulo boundary, so $`H^n(X; G)` is "almost isomorphic" to $`\operatorname{Hom}(H_n(X), G)`.
The universal coefficient theorem states this precisely, with the "error term" being exactly $`\operatorname{Ext}(H_{n-1}(X), G)`: if the region $`e^k` has a boundary divisible by $`n`, then we care about the value assigned to $`e^k` modulo $`n`, and this is what produces the $`\operatorname{Ext}` contribution.

# Relative cohomology groups

One can also define relative cohomology groups in the obvious way: dualize the chain complex $`\dots \xrightarrow{\partial} C_1(X, A) \xrightarrow{\partial} C_0(X, A) \to 0` to obtain a cochain complex, and take its cohomology.

:::DEFINITION
The groups thus obtained are the *relative cohomology groups* and are denoted $`H^n(X, A; G)`.
:::

:::DEFINITION
The *reduced cohomology groups* of a nonempty space $`X`, denoted $`\widetilde H^n(X; G)`, are defined to be $`H^n(X, \{\ast\}; G)` for some point $`\ast \in X`.
:::

# Problems

:::PROBLEM "Wedge product cohomology"
For any $`G` and $`n` we have $$`\widetilde H^n(X \vee Y; G) \cong \widetilde H^n(X; G) \oplus \widetilde H^n(Y; G).`
:::

:::PROBLEM "Cohomology over a field is a dual"
Prove that for a field $`F` of characteristic zero and a space $`X` with finitely generated homology groups: $$`H^k(X, F) \cong \left( H_k(X) \right)^\vee.`
Thus over fields cohomology is the dual of homology.
:::

:::PROBLEM "$\\mathbb{Z}/2$-cohomology of $\\mathbb{RP}^n$"
Prove that $$`H^m(\mathbb{RP}^n, \mathbb{Z}/2) \cong \begin{cases} \mathbb{Z} & m = 0, \text{ or } m \text{ is odd and } m = n \\ \mathbb{Z}/2 & 0 < m < n \text{ and } m \text{ is odd} \\ 0 & \text{otherwise}. \end{cases}`
:::
