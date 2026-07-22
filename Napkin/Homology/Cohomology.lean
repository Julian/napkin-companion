import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Napkin.Missing.Cochains

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing
open Napkin.Missing.Cochain
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

:::figure "figures/homology/cohomology-functorial.svg"
A map $`f \colon X \to Y` induces $`f^* \colon H^n(Y; G) \to H^n(X; G)`, reversing direction.
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

# Explanation for universal coefficient theorem

There is so much unexplained symbols and formulas in the previous chapter that may make you scream:

:::quote
I don't care if $`\mathbb{CP}^2` and $`S^2 \vee S^4` are distinct anymore! What are these spaces anyway?
:::

Nevertheless, it is not all that difficult.
There are two key points to be read from the theorem:

- Even though $`H_n(A_\bullet) = 0`, it is still possible for $`H^n(A_\bullet; G) \neq 0` if $`\operatorname{Ext}(H_{n-1}(A_\bullet), G) \neq 0`.
- $`H^n(A_\bullet; G)` is uniquely determined by $`H_n(A_\bullet)` and $`G`, regardless of what $`A_\bullet` is, as long as each $`A_n` is free.

Which means: if you wish, you can forget about the formula in the universal coefficient theorem, and use the cellular chain complex $`\operatorname{Cells}_\bullet(X)` to compute cohomology by dualizing it.
After all, the cellular chain complex and the singular chain complex are both free and have the same homology groups, so by the universal coefficient theorem they must have the same cohomology groups.

Geometrically, a cocycle modulo coboundary can be "evaluated" on a cycle modulo boundary, so $`H^n(X; G)` is "almost isomorphic" to $`\operatorname{Hom}(H_n(X), G)`.
The universal coefficient theorem states this precisely, with the "error term" being exactly $`\operatorname{Ext}(H_{n-1}(X), G)`: if the region $`e^k` has a boundary divisible by $`n`, then we care about the value assigned to $`e^k` modulo $`n`, and this is what produces the $`\operatorname{Ext}` contribution.

# Visualization of cohomology groups

We try to make sense of $`C^n(X; G)` and $`H^n(X; G)`, for higher values of $`n`.
As above, $`C_n(X; G)` is the free abelian group on $`n`-simplices on $`X`, so an element $`f \in C^n(X; G)` is a function that takes each $`n`-simplex to an element of $`G` (and extends linearly to all of $`C_n(X; G)`).
This assignment of value need not have any nice properties — recall that a $`n`-simplex is simply a (continuous) map $`\sigma \colon \Delta^n \to X`, and different maps $`\sigma_1` and $`\sigma_2` are considered different even though $`\operatorname{img} \sigma_1 = \operatorname{img} \sigma_2`.
In particular,

- If $`[v_0, v_1, v_2]` is a singular simplex, it need not be the case that $`f([v_0, v_1, v_2]) + f([v_0, v_2, v_1]) = 0`.
- A singular $`n`-simplex ($`n \geq 1`) with image contained in a point need not be mapped to $`0` by $`f`.

But it _does not matter_ that elements of $`C_n(X)` aren't this nice!
We will see below why this is the case.
In the homology case, we defined $$`Z_n(X) \coloneqq \ker\left( C_n(X) \xrightarrow{\partial} C_{n-1}(X) \right), \quad B_n(X) \coloneqq \operatorname{img}\left( C_{n+1}(X) \xrightarrow{\partial} C_n(X) \right), \quad H_n(X) \coloneqq Z_n(X)/B_n(X).`
Elements of $`Z_n(X)` and $`B_n(X)` are called cycles and boundaries respectively, with the obvious geometrical interpretation.
So, $$`H_n(X) = \frac{n\text{-cycles}}{n\text{-boundaries}}.`
For the current section, we will temporarily define $$`Z^n(X; G) \coloneqq \ker\left( C^n(X; G) \xrightarrow{\delta} C^{n+1}(X; G) \right), \quad B^n(X; G) \coloneqq \operatorname{img}\left( C^{n-1}(X; G) \xrightarrow{\delta} C^n(X; G) \right),`
with $`H^n(X; G) \coloneqq Z^n(X; G)/B^n(X; G)`.
For this section, we will call elements of $`Z^n(X; G)` the *cocycles* and elements of $`B^n(X; G)` the *coboundaries* respectively.
Once again, $$`H^n(X; G) = \frac{n\text{-cocycles}}{n\text{-coboundaries}}.`

It's less clear geometrically why the elements are named as above, but if we assume the group $`G` is a _field_ (where the group operation is the addition operation in the field), then we have:

- a $`n`-cocycle is a map that sends every $`n`-boundary to $`0 \in G`;
- a $`n`-coboundary is a map that sends every $`n`-cycle to $`0 \in G`.

The first statement is clear (definition chasing), the second statement is only generally true in one direction (that a coboundary sends every cycle to $`0`; but a map that sends every cycle to $`0` need not be a coboundary — we will see this later on with the Klein bottle example).

Let us see what a $`n`-cocycle must look like.
First,

:::MORAL
Homotopic chains with the same boundary are mapped to the same value by cocycles.
:::

We defined what it means for two $`k`-simplices to be homotopic when discussing higher homotopy groups — in the current situation, we require in addition that the boundaries are always fixed.
For instance, two $`1`-simplices from $`p` to $`q` that can be continuously deformed into one another (rel endpoints) are homotopic, while a $`1`-simplex forced to go around a hole in the space is not.

:::figure "figures/homology/cohomology-homotopic-simplices.svg"
The blue and orange $`1`-simplices from $`p` to $`q` are homotopic; the red one, going around the hole, is not.
:::

Proof is not difficult — you just need to show that the difference between two homotopic $`k`-simplices is the boundary of something (their interior!), and write the interior as the sum of some $`k+1`-simplices.
(Hint: the easiest way is actually to write the interior as the difference of two $`k+1`-simplices instead, and be careful of vertex ordering issues.)

:::EXERCISE
Finish the proof.
:::

A typical $`1`-cocycle assigns a value to each $`1`-simplex (arrow), subject to the constraint that a cycle must be mapped to $`0`; so the values around any closed loop must cancel.

:::figure "figures/homology/cohomology-one-cocycle.svg"
A typical $`1`-cocycle: each arrow carries its assigned value, and every cycle sums to $`0`.
:::

Now, the next observation is that:

:::MORAL
If we only consider cocycles modulo coboundaries, we basically only care about values assigned to the cycles.
:::

Why?
Remember that a $`k`-coboundary is the $`\delta` of some $`(k-1)`-cochain.
Given a $`0`-cochain that assigns the value $`1` to a single vertex,

:::figure "figures/homology/cohomology-zero-cochain.svg"
A $`0`-cochain assigning the value $`1` to one vertex.
:::

its $`\delta` assigns $`\pm 1` to each edge touching that vertex (with sign according to orientation).

:::figure "figures/homology/cohomology-delta-cochain.svg"
The coboundary $`\delta` of that $`0`-cochain, spreading $`\pm 1` along the incident edges.
:::
So, roughly speaking,

:::MORAL
By adding or subtracting a coboundary to a given cochain, we can adjust the value assigned to most chains however we want.
:::

I said "most chains" because, if the chains form a _cycle_, adding a coboundary won't let us change its assigned value.
Fortunately,

- Cycles that are _boundaries_ always get assigned the value $`0`.
- Homotopic cycles get assigned the same value.
  As a generalization, in fact, cycles that are homologous (i.e. they get mapped to the same value under the map $`Z_k(X) \twoheadrightarrow H_k(X)`) are assigned the same value.

Therefore,

:::MORAL
Knowing the value of a cocycle on each "cycle modulo boundary" almost determines that cocycle, modulo coboundaries.
:::

In symbols: $`H^n(X; G)` is "almost isomorphic" to $`\operatorname{Hom}(H_n(X), G)`.
In other words, a cocycle modulo coboundary can be "evaluated" on a cycle modulo boundary.

This is precisely what the universal coefficient theorem states, although it says something more: the "error term" is exactly $`\operatorname{Ext}(H_{n-1}(X), G)`.

Why would the error term exist?
We had an example above, computing $`H^2(K; G)` for $`K` the Klein bottle.
Let us work through it geometrically, assume $`G = \mathbb{Z}` for now.

A typical $`2`-cochain $`f \in C^2(K; \mathbb{Z})` assigns a value to each $`2`-simplex.

:::figure "figures/homology/cohomology-klein-2cochain.svg"
A $`2`-cochain $`f` on the Klein bottle, assigning values to the two triangles of the square.
:::

As with the $`0`-cochain above, the value assigned to a particular simplex doesn't matter: we can "transfer" the assigned value between the two triangles of the square by adding a coboundary.

:::figure "figures/homology/cohomology-klein-coboundary.svg"
Adding a coboundary $`\delta` transfers value between the two triangles without changing the total.
:::
So, we may just say that the value assigned to the whole surface of the Klein bottle is (say) $`3`; formally, letting $`e^2_K \in C_2(K)` be the sum of the two $`2`-simplices, we can write $`f(e^2_K) = 3`.

However, the boundary of the $`2`-chain corresponding to the whole surface of the Klein bottle is $`2` times the blue edge, so $`\delta` of the $`1`-cochain whose value on the blue edge is $`1` will assign the value $`2` to $`e^2_K`.
In symbols: let $`e^1_b \in C_1(K)` be the blue edge, pick $`g \in C^1(K; \mathbb{Z})` such that $`g(e^1_b) = 1`, then $`\delta(g)(e^2_K) = 2`.

:::figure "figures/homology/cohomology-klein-g-cochain.svg"
The $`1`-cochain $`g` with value $`1` on the blue edge; its coboundary assigns $`2` to the whole surface $`e^2_K`.
:::
Even though $`e^2_K` is not a cycle, we still need to care about its assigned value modulo $`2`!
Because adding or subtracting the coboundary $`\delta(g)` can only adjust its values in increments of $`2`.

Therefore,

:::MORAL
If the region $`e^k \in C_k(X)` has a boundary $`\partial e^k \in C_{k-1}(X)` divisible by $`n`, then we care about the value assigned to $`e^k`, modulo $`n`.
:::

This explains where the error term $`\operatorname{Ext}(H_{n-1}(X), G)` comes from.

We have another comparison with de Rham cohomology in the cohomology-ring chapter — in that case, the group $`G` is a field, $`\mathbb{R}`, so $`\operatorname{Ext}(H_{n-1}(X), G)` is always zero.

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

# Formalization

:::LEANCOMPANION
:::

## Cochain complexes

Mathlib's `CochainComplex` is the special case of `HomologicalComplex` whose differential _raises_ the degree by one — the mirror image of `ChainComplex`.
Fixing an ambient category `V` with a zero morphism, a cochain complex indexed by $`\mathbb{N}` is a term of `CochainComplex V ℕ`.

```lean
example {V : Type*} [Category V] [Limits.HasZeroMorphisms V] :
    Type _ := CochainComplex V ℕ
```

Because the indexing is set up so that consecutive degrees compose to zero, the defining relation $`\delta^2 = 0` holds for any three degrees, recorded as `HomologicalComplex.d_comp_d`.
Its cohomology is computed by the very same `HomologicalComplex.homology` used for chain complexes.

```lean
noncomputable example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    [CategoryWithHomology V] (A : CochainComplex V ℕ) (n : ℕ) : V :=
  A.homology n
```

Show that the differentials of a cochain complex compose to zero; `A.d_comp_d i j k`, the `HomologicalComplex.d_comp_d` above specialized to `A`, closes it.

```lean
example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    (A : CochainComplex V ℕ) (i j k : ℕ) :
    A.d i j ≫ A.d j k = 0 := by
  sorry
```

## Cohomology of spaces

Mathlib does not build the singular cochain complex $`C^\bullet(X; G)` of a topological space, nor the singular cohomology groups $`H^n(X; G)`.
Rebuilding the chain side — a singular simplex, its faces, the boundary $`\partial`, and $`\partial^2 = 0` — is carried out in `Napkin.Missing.Chains`; dualizing it is `Napkin.Missing.Cochains`.
A cochain `Cochain X G n` is by definition an element of the dual of the chain group, a homomorphism `Chain X n →+ G`: exactly "a value in $`G` for each singular $`n`-simplex, extended linearly".

```lean
example {X : Type*} {G : Type*} [AddCommGroup G] (n : ℕ) :
    Cochain X G n = (Chain X n →+ G) := rfl
```

The coboundary $`\delta` is the transpose of the boundary: $`(\delta c)(\sigma) = c(\partial\sigma)`, so `coboundary c` is `c` pre-composed with the boundary map.

```lean
example {X : Type*} {G : Type*} [AddCommGroup G] {n : ℕ}
    (c : Cochain X G n) (a : Chain X (n + 1)) :
    coboundary c a = c (Chain.boundary a) := rfl
```

The defining relation $`\delta^2 = 0` of a cochain complex is then just the transpose of $`\partial^2 = 0`: since $`(\delta^2 c)(\sigma) = c(\partial^2 \sigma) = c(0) = 0`, two coboundaries in a row annihilate every cochain.

```lean
example {X : Type*} {G : Type*} [AddCommGroup G] {n : ℕ}
    (c : Cochain X G n) : coboundary (coboundary c) = 0 :=
  coboundary_coboundary c
```

With $`\delta^2 = 0` in hand the coboundaries sit inside the cocycles, and the quotient is the cohomology group; `Cohomology X G n` models $`H^{n+1}(X; G)` (the degree is shifted because $`H^0` has no incoming coboundary), and it is a genuine abelian group.

```lean
noncomputable example {X : Type*} {G : Type*} [AddCommGroup G] (n : ℕ) :
    AddCommGroup (Cohomology X G n) := inferInstance
```

The coboundary is additive — this is the sense in which $`\delta` is linear.
Prove it; the shim records this same statement as `coboundary_add`.

```lean
example {X : Type*} {G : Type*} [AddCommGroup G] {n : ℕ}
    (c₁ c₂ : Cochain X G n) :
    coboundary (c₁ + c₂) = coboundary c₁ + coboundary c₂ := by
  sorry
```

The prototype claimed a $`0`-cochain in $`\ker\delta` is constant on path components; combinatorially, $`\delta c = 0` forces `c` to agree across the two endpoints of every $`1`-simplex $`[v_0, v_1]`, because $`(\delta c)([v_0, v_1]) = c([v_1]) - c([v_0])`.
To even state this we need to name the vertices of a $`1`-simplex.
A `Simplex X n` is the tuple of its $`n + 1` vertices `Fin (n + 1) → X`, so a $`1`-simplex `v : Simplex X 1` has endpoints `v 0` and `v 1`.

```lean
example {X : Type*} (n : ℕ) : Simplex X n = (Fin (n + 1) → X) := rfl
```

The generating chain $`1 \cdot \sigma` is `Chain.ofSimplex σ`, and the boundary of the edge $`[v_0, v_1]` is the $`0`-chain $`\{v_1\} - \{v_0\}`, recorded as `Chain.boundary_one`.

```lean
example {X : Type*} (v : Simplex X 1) :
    Chain.boundary (Chain.ofSimplex v)
      = Chain.ofSimplex (fun _ => v 1) - Chain.ofSimplex (fun _ => v 0) :=
  Chain.boundary_one v
```

Prove this local constancy; the shim records it as `cocycle_zero_locally_constant`.

```lean
example {X : Type*} {G : Type*} [AddCommGroup G] {c : Cochain X G 0}
    (h : coboundary c = 0) (v : Simplex X 1) :
    c (Chain.ofSimplex fun _ => v 1)
      = c (Chain.ofSimplex fun _ => v 0) := by
  sorry
```

Underlying all of this is dualizing a _single_ map by $`\operatorname{Hom}(-, G)`, which Mathlib does have.
Over a commutative ring `R` the dual $`\operatorname{Hom}(M, R)` is `Module.Dual R M`, and a linear map $`M \to N` dualizes — reversing direction — to `LinearMap.dualMap`.

```lean
example (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Module.Dual R N →ₗ[R] Module.Dual R M := f.dualMap
```

Evaluating a dualized functional recovers "evaluate the cochain on the image of the chain": $`f^\vee(g)` sends `x` to $`g(f\,x)`, which is `LinearMap.dualMap_apply`.

```lean
example (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (g : Module.Dual R N) (x : M) : f.dualMap g x = g (f x) :=
  LinearMap.dualMap_apply f g x
```

The exercise on functoriality asked you to read $`\operatorname{Hom}(-, G)` as a contravariant functor: a composite $`g \circ f` dualizes with the order reversed.
Prove that dualization is contravariant; `LinearMap.dualMap_comp_dualMap` states the reversed equation, so its `.symm` closes it.

```lean
example (R M N P : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (g.comp f).dualMap = f.dualMap.comp g.dualMap := by
  sorry
```

## Universal coefficient theorem

Mathlib does have $`\operatorname{Ext}` groups (in `Mathlib.Algebra.Homology.DerivedCategory.Ext`), but they are set up in the general derived-category framework rather than the one-step free-resolution recipe used here, and the universal coefficient theorem itself is not part of the library.
The short exact sequence it produces lives, abstractly, in the type of three-term complexes `ShortComplex`.

```lean
example {V : Type*} [Category V] [Limits.HasZeroMorphisms V] :
    Type _ := ShortComplex V
```

Over a field the $`\operatorname{Ext}` term vanishes, so cohomology is exactly the dual of homology — the content of the problem "cohomology over a field is a dual".
The algebraic fact that makes this an honest isomorphism for finitely generated homology is that a finite-dimensional vector space and its dual have the same dimension.
Prove it; `Subspace.dual_finrank_eq` is exactly this equality of dimensions.

```lean
example (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Module.finrank F (Module.Dual F V) = Module.finrank F V := by
  sorry
```
