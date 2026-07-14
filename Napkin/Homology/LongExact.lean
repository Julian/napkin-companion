import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open CategoryTheory

set_option pp.rawOnError true

#doc (Manual) "The long exact sequence" =>

%%%
file := "The-long-exact-sequence"
%%%

In this chapter we introduce the key fact about chain complexes that will allow us to compute the homology groups of any space: the so-called "long exact sequence".

For those that haven't read about abelian categories: a sequence of morphisms of abelian groups $$`\dots \to G_{n+1} \to G_n \to G_{n-1} \to \dots`
is *exact* if the image of any arrow is equal to the kernel of the next arrow.
In particular,

- The map $`0 \to A \to B` is exact if and only if $`A \to B` is injective.
- the map $`A \to B \to 0` is exact if and only if $`A \to B` is surjective.

(On that note: what do you call a chain complex whose homology groups are all trivial?)
A short exact sequence is one of the form $`0 \to A \hookrightarrow B \twoheadrightarrow C \to 0`.

:::aside
Mathlib works with these one degree at a time.
A three-term complex $`A \to B \to C` is a {name}`CategoryTheory.ShortComplex`, and {name}`CategoryTheory.ShortComplex.Exact` is the predicate that its single spot is exact; {name}`CategoryTheory.ShortComplex.ShortExact` bundles this together with $`A \to B` mono and $`B \to C` epi, exactly the "$`0 \to A \hookrightarrow B \twoheadrightarrow C \to 0`" above.

```lean
example {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) : Prop :=
  S.ShortExact
```
:::

# Short exact sequences and four examples

:::PROTOTYPE
Relative sequence and Mayer–Vietoris sequence.
:::

Let $`\mathcal{A} = \mathbf{AbGrp}`.
Recall that we defined a morphism of chain complexes in $`\mathcal{A}` already.

:::DEFINITION
Suppose we have a map of chain complexes $$`0 \to A_\bullet \xrightarrow{f} B_\bullet \xrightarrow{g} C_\bullet \to 0`
It is said to be *short exact* if _each row_ $`0 \to A_n \hookrightarrow B_n \twoheadrightarrow C_n \to 0` of the corresponding diagram is short exact.
:::

:::figure "figures/homology/longexact-ses-double-ladder.svg"
A short exact sequence of chain complexes: every row $`0 \to A_n \hookrightarrow B_n \twoheadrightarrow C_n \to 0` is short exact.
:::

:::MORAL
This basically means $`C_\bullet = B_\bullet / A_\bullet`, for suitable definition of $`/` on chain complexes.
:::

This agrees with the definition of exact sequences from the abstract-algebra chapters.

:::EXAMPLE "Mayer–Vietoris short exact sequence"
Let $`X = U \cup V` be an open cover.
For each $`n` consider the maps $`c \mapsto (c, -c)` from $`C_n(U \cap V)` to $`C_n(U) \oplus C_n(V)`, and $`(c, d) \mapsto c + d` from $`C_n(U) \oplus C_n(V)` to $`C_n(U + V)`.
One can easily see (by taking a suitable basis) that the kernel of the latter map is exactly the image of the first map.
This generates a short exact sequence $$`0 \to C_\bullet(U \cap V) \hookrightarrow C_\bullet(U) \oplus C_\bullet(V) \twoheadrightarrow C_\bullet(U + V) \to 0.`
:::

:::figure "figures/homology/longexact-uv-splitting.svg"
The Mayer–Vietoris maps $`c \mapsto (c, -c)` and $`(c, d) \mapsto c + d`.
:::

:::EXAMPLE "Augmented Mayer–Vietoris sequence"
We can _augment_ each of the chain complexes in the Mayer–Vietoris sequence as well, by appending a bottom row $`0 \to \mathbb{Z} \to \mathbb{Z} \oplus \mathbb{Z} \to \mathbb{Z} \to 0` via the maps $`\varepsilon`.
In other words we modify the above into $$`0 \to \widetilde C_\bullet(U \cap V) \hookrightarrow \widetilde C_\bullet(U) \oplus \widetilde C_\bullet(V) \twoheadrightarrow \widetilde C_\bullet(U + V) \to 0`
where $`\widetilde C_\bullet` is the augmented chain complex.
:::

:::figure "figures/homology/longexact-uv-augmented.svg"
Augmenting the Mayer–Vietoris sequence with the bottom row $`0 \to \mathbb{Z} \to \mathbb{Z} \oplus \mathbb{Z} \to \mathbb{Z} \to 0`.
:::

:::EXAMPLE "Relative chain short exact sequence"
Since $`C_n(X, A) \coloneqq C_n(X) / C_n(A)`, we have a short exact sequence $$`0 \to C_\bullet(A) \hookrightarrow C_\bullet(X) \twoheadrightarrow C_\bullet(X, A) \to 0`
for every space $`X` and subspace $`A`.
This can be augmented: we get $$`0 \to \widetilde C_\bullet(A) \hookrightarrow \widetilde C_\bullet(X) \twoheadrightarrow C_\bullet(X, A) \to 0`
by adding a final row with the identity $`\mathbb{Z} \xrightarrow{\operatorname{id}} \mathbb{Z}`.
:::

:::figure "figures/homology/longexact-relative-augmented.svg"
The augmented relative short exact sequence, with bottom row $`\mathbb{Z} \xrightarrow{\operatorname{id}} \mathbb{Z}`.
:::

# The long exact sequence of homology groups

Consider a short exact sequence $`0 \to A_\bullet \xrightarrow{f} B_\bullet \xrightarrow{g} C_\bullet \to 0`.
Now, we know that we get induced maps of homology groups, i.e. we have maps $`f_\ast \colon H_n(A_\bullet) \to H_n(B_\bullet)` and $`g_\ast \colon H_n(B_\bullet) \to H_n(C_\bullet)` for every $`n`.
But the theorem is that we can string these all together, taking each $`H_{n+1}(C_\bullet)` to $`H_n(A_\bullet)`.

:::figure "figures/homology/longexact-h-grid.svg"
The induced maps $`f_\ast`, $`g_\ast` arranged in a grid, before stringing them together.
:::

:::THEOREM "Short exact implies long exact"
Let $`0 \to A_\bullet \xrightarrow{f} B_\bullet \xrightarrow{g} C_\bullet \to 0` be _any_ short exact sequence of chain complexes we like.
Then there is an _exact_ sequence $$`\dots \to H_{n+1}(C_\bullet) \xrightarrow{\partial} H_n(A_\bullet) \xrightarrow{f_\ast} H_n(B_\bullet) \xrightarrow{g_\ast} H_n(C_\bullet) \xrightarrow{\partial} H_{n-1}(A_\bullet) \to \dots.`
This is called a *long exact sequence* of homology groups.
:::

:::figure "figures/homology/longexact-les-zigzag.svg"
The connecting maps $`\partial` weave the grid into a single zigzag long exact sequence.
:::

:::PROOF
A very long diagram chase, valid over any abelian category.
(Alternatively, it's actually possible to use the snake lemma twice.)
:::

:::aside
This is one of the anchor theorems of homological algebra in Mathlib.
From a short exact sequence of homological complexes, the connecting maps $`\partial` and the exactness of the resulting sequence are assembled in `Mathlib.Algebra.Homology.HomologySequence`; the connecting map itself is built from the snake lemma, which lives as {name}`CategoryTheory.ShortComplex.Exact` data for the relevant diagrams.
:::

:::REMARK
The map $`\partial \colon H_n(C_\bullet) \to H_{n-1}(A_\bullet)` can be written explicitly as follows.
We need to take every cycle in $`C_n` to a cycle in $`A_{n-1}`.
Suppose $`c \in C_n` is a cycle (so $`\partial_C(c) = 0`).
By surjectivity, there is a $`b \in B_n` with $`g_n(b) = c`, which maps down to $`\partial_B(b)`.
Now, the image of $`\partial_B(b)` under $`g_{n-1}` is zero by commutativity of the square, and so we can pull back under $`f_{n-1}` to get a unique element of $`A_{n-1}` (by exactness at $`B_{n-1}`).
In summary: we go "_left, down, left_" to go from $`c` to $`a`.
:::

:::figure "figures/homology/longexact-connecting-square.svg"
The connecting map $`\partial`: from a cycle $`c \in C_n`, chase left–down–left to a cycle $`a \in A_{n-1}`.
:::

:::figure "figures/homology/longexact-diagram-chase.svg"
The same chase on elements: $`b \mapsto c`, $`a \mapsto \partial_B(b)`, using $`g_{n-1}(\partial_B b) = 0`.
:::

:::EXERCISE
Check quickly that the recovered $`a` is actually a cycle, meaning $`\partial_A(a) = 0`.
(You'll need another row, and the fact that $`\partial_B^2 = 0`.)
:::

The final word is that:

:::MORAL
Short exact sequences of chain complexes give long exact sequences of homology groups.
:::

In particular, let us take the four examples given earlier.

:::EXAMPLE "Mayer–Vietoris long exact sequence, provisional version"
The Mayer–Vietoris ones give, for $`X = U \cup V` an open cover, $$`\dots \to H_n(U \cap V) \to H_n(U) \oplus H_n(V) \to H_n(U + V) \to H_{n-1}(U \cap V) \to \dots.`
and its reduced version $$`\dots \to \widetilde H_n(U \cap V) \to \widetilde H_n(U) \oplus \widetilde H_n(V) \to \widetilde H_n(U + V) \to \widetilde H_{n-1}(U \cap V) \to \dots.`
:::

This version is "provisional" because in the next section we will replace $`H_n(U + V)` and $`\widetilde H_n(U + V)` with something better.
As for the relative homology sequences, we have:

:::THEOREM "Long exact sequence for relative homology"
Let $`X` be a space, and let $`A \subseteq X` be a subspace.
There are long exact sequences $$`\dots \to H_n(A) \to H_n(X) \to H_n(X, A) \to H_{n-1}(A) \to \dots.`
and $$`\dots \to \widetilde H_n(A) \to \widetilde H_n(X) \to H_n(X, A) \to \widetilde H_{n-1}(A) \to \dots.`
:::

The exactness of these sequences will give *tons of information* about $`H_n(X)` if only we knew something about what $`H_n(U + V)` or $`H_n(X, A)` looked like.
This is the purpose of the next chapter.

# The Mayer–Vietoris sequence

:::PROTOTYPE
The computation of $`H_n(S^m)` by splitting $`S^m` into two hemispheres.
:::

Now that we have done so much algebra, we need to invoke some geometry.
There are two major geometric results in this book.
One is the excision theorem, which we discuss next chapter.
The other we present here, which will let us take advantage of the Mayer–Vietoris sequence.
The proofs are somewhat involved and are thus omitted; see {cite}`ref:hatcher` for details.

The first theorem is that the notation $`H_n(U + V)` that we have kept until now is redundant, and can be replaced with just $`H_n(X)`:

:::THEOREM "Open cover homology theorem"
Consider the inclusion $`\iota \colon C_\bullet(U + V) \hookrightarrow C_\bullet(X)`.
Then $`\iota` induces an isomorphism $$`H_n(U + V) \cong H_n(X).`
:::

:::REMARK
In fact, this is true for any open cover (even uncountable), not just those with two covers $`U \cup V`.
But we only state the special case with two open sets, because this is what is needed for the Mayer–Vietoris example.
:::

So, the Mayer–Vietoris short exact sequence together with the above theorem implies, after replacing all the $`H_n(U + V)`'s with $`H_n(X)`'s:

:::THEOREM "Mayer–Vietoris long exact sequence"
If $`X = U \cup V` is an open cover, then we have long exact sequences $$`\dots \to H_n(U \cap V) \to H_n(U) \oplus H_n(V) \to H_n(X) \to H_{n-1}(U \cap V) \to \dots.`
and $$`\dots \to \widetilde H_n(U \cap V) \to \widetilde H_n(U) \oplus \widetilde H_n(V) \to \widetilde H_n(X) \to \widetilde H_{n-1}(U \cap V) \to \dots.`
:::

At long last, we can compute the homology groups of the spheres.

:::THEOREM "The homology groups of $S^m$"
For integers $`m` and $`n`, $$`\widetilde H_n(S^m) \cong \begin{cases} \mathbb{Z} & n = m \\ 0 & \text{otherwise}. \end{cases}`
The generator $`\widetilde H_n(S^n)` is an $`n`-cell which covers $`S^n` exactly once (for example, the generator for $`\widetilde H_1(S^1)` is a loop which wraps around $`S^1` once).
:::

::::PROOF
This one's fun, so I'll only spoil the case $`m = 1`, and leave the rest to you.
Decompose the circle $`S^1` into two arcs $`U` and $`V`.

:::figure "figures/homology/longexact-mv-cover-s1.svg"
The circle $`S^1` covered by two arcs, $`U` (blue) and $`V` (red).
:::

Each of $`U` and $`V` is contractible, so all their reduced homology groups vanish.
Moreover, $`U \cap V` is homotopy equivalent to two points, hence $$`\widetilde H_n(U \cap V) \cong \begin{cases} \mathbb{Z} & n = 0 \\ 0 & \text{otherwise}. \end{cases}`
Now consider again the segment of the long exact sequence $$`\dots \to \underbrace{\widetilde H_n(U) \oplus \widetilde H_n(V)}_{= 0} \to \widetilde H_n(S^1) \xrightarrow{\partial} \underbrace{\widetilde H_{n-1}(U \cap V)}_{\cong \mathbb{Z} \text{ or } 0} \to \underbrace{\widetilde H_{n-1}(U) \oplus \widetilde H_{n-1}(V)}_{= 0} \to \dots.`
From this we derive that $`\widetilde H_n(S^1)` is $`\mathbb{Z}` for $`n = 1` and $`0` elsewhere.

It remains to analyze the generators of $`\widetilde H_1(S^1)`.
The isomorphism was given by the connecting homomorphism $`\partial`, which is given by a "left, down, left" procedure.
Marking points $`a` and $`b` in the two disjoint paths of $`U \cap V`, the cycle $`a - b` represents a generator of $`H_0(U \cap V)`, and letting $`c` and $`d` be the chains joining $`a` and $`b` with $`c` contained in $`U` and $`d` contained in $`V`, one finds $`\partial(c - d) = a - b`, so $`c - d` is a generator.
Thus $`c - d` is (in $`H^1(S^1)`) equivalent to the loop $`\gamma` wrapping around $`S^1` once, counterclockwise.

:::figure "figures/homology/longexact-mv-s1-cd.svg"
The chains $`c` and $`d` join $`a` to $`b` inside $`U` and $`V`; the cycle $`c - d` generates $`\widetilde H_1(S^1)`.
:::

:::figure "figures/homology/longexact-mv-square1.svg"
The relevant corner of the Mayer–Vietoris diagram used to compute $`\partial`.
:::

:::figure "figures/homology/longexact-mv-cd-map.svg"
Chasing $`(c, d) \mapsto c - d` and $`a - b \mapsto (a - b, a - b)` through the diagram.
:::
::::

Thus, the key idea in Mayer–Vietoris is that

:::MORAL
Mayer–Vietoris lets us compute $`H_n(X)` by splitting $`X` into two open sets.
:::

Here are some more examples.

:::PROPOSITION "The homology groups of the figure eight"
Let $`X = S^1 \vee S^1` be the figure eight.
Then $$`\widetilde H_n(X) \cong \begin{cases} \mathbb{Z}^{\oplus 2} & n = 1 \\ 0 & \text{otherwise}. \end{cases}`
The generators for $`\widetilde H_1(X)` are the two loops of the figure eight.
:::

::::PROOF
Again, for simplicity we work with reduced homology groups.
Let $`U` be the "left" half of the figure eight plus a little bit of the right, and $`V` symmetrically.

:::figure "figures/homology/longexact-fig8-cover.svg"
The figure eight covered by $`U` (the left loop plus a bit of the right) and, symmetrically, $`V`.
:::
In this case $`U \cap V` is contractible, while each of $`U` and $`V` is homotopic to $`S^1`.
Thus, we can read a segment of the long exact sequence as $$`\dots \to \underbrace{\widetilde H_n(U \cap V)}_{= 0} \to \widetilde H_n(U) \oplus \widetilde H_n(V) \to \widetilde H_n(X) \to \underbrace{\widetilde H_{n-1}(U \cap V)}_{= 0} \to \dots.`
So we get that $`\widetilde H_n(X) \cong \widetilde H_n(S^1) \oplus \widetilde H_n(S^1)`.
The claim about the generators follows from the fact that the generators of $`\widetilde H_n(X)` are the generators of $`\widetilde H_n(U)` and $`\widetilde H_n(V)`.
::::

Up until now, we have been very fortunate that we have always been able to make certain parts of the space contractible.
This is not always the case, and in the next example we will have to actually understand the maps in question to complete the solution.

:::PROPOSITION "Homology groups of the torus"
Let $`X = S^1 \times S^1` be the torus.
Then $$`\widetilde H_n(X) = \begin{cases} \mathbb{Z}^{\oplus 2} & n = 1 \\ \mathbb{Z} & n = 2 \\ 0 & \text{otherwise}. \end{cases}`
:::

::::PROOF
We represent the torus as a square with its edges identified.
Consider $`U` and $`V` as two overlapping vertical bands; note that $`V` is connected due to the identification of the left and right edges.
In the three dimensional picture, $`U` and $`V` are two cylinders which together give the torus.

:::figure "figures/homology/longexact-excision-square.svg"
The torus as a square, covered by a middle band $`U` and the (wrap-around) side band $`V`.
:::
This time, $`U` and $`V` are each homotopic to $`S^1`, and the intersection $`U \cap V` is the disjoint union of two circles: thus $`\widetilde H_1(U \cap V) \cong \mathbb{Z} \oplus \mathbb{Z}`, and $`\widetilde H_0(U \cap V) \cong \mathbb{Z}`.

For $`n \ge 3`, both neighbours in the sequence vanish, so $`H_n(X) \cong 0`.
Also, $`H_0(X) \cong \mathbb{Z}` since $`X` is path-connected.
So it remains to compute $`H_2(X)` and $`H_1(X)`.

For $`H_2(X)`, consider the segment $$`\underbrace{\widetilde H_2(U) \oplus \widetilde H_2(V)}_{= 0} \to \widetilde H_2(X) \xrightarrow{\partial} \underbrace{\widetilde H_1(U \cap V)}_{\cong \mathbb{Z}^2} \xrightarrow{\phi} \underbrace{\widetilde H_1(U) \oplus \widetilde H_1(V)}_{\cong \mathbb{Z}^2}.`
The presence of the zero term makes $`\partial` injective, so $`\widetilde H_2(X) \cong \ker\phi`.
Recalling that the map $`C_\bullet(U \cap V) \to C_\bullet(U) \oplus C_\bullet(V)` was $`c \mapsto (c, -c)`, the two generators $`z_1, z_2` of $`\widetilde H_1(U \cap V)` are sent to $`(\alpha_U, -\alpha_V)` each, giving the matrix $$`\phi = \begin{bmatrix} 1 & 1 \\ -1 & -1 \end{bmatrix}.`
(The signs may differ on which direction you pick for the generators; note that $`\mathbb{Z}` has two possible generators.)
Note that $`z_1`, $`z_2`, $`\alpha_U`, $`\alpha_V` are elements of the homology group, so you can move the paths around a bit — for instance, as elements of $`\widetilde H_1(U)`, the chain drawn as $`z_1` and $`\alpha_U` represents the same element.

:::figure "figures/homology/longexact-excision-chains.svg"
The generators $`z_1, z_2` of $`\widetilde H_1(U \cap V)` and the loops $`\alpha_U, \alpha_V`.
:::

:::figure "figures/homology/longexact-mv-torus-les.svg"
The segment of the Mayer–Vietoris sequence computing $`\widetilde H_2(X) \cong \mathbb{Z}`.
:::

:::figure "figures/homology/longexact-mv-square2.svg"
The diagram corner witnessing the map $`\phi` above.
:::
So $`\ker\phi = \left< z_1 - z_2 \right> \cong \mathbb{Z}`, and $`\widetilde H_2(X) \cong \mathbb{Z}`.
We also note $`\operatorname{img}\phi \cong \mathbb{Z}` and the quotient by it is $`\mathbb{Z}` too.

For $`\widetilde H_1(X)` we have the segment $$`\xrightarrow{\phi} \underbrace{\widetilde H_1(U) \oplus \widetilde H_1(V)}_{\cong \mathbb{Z}^2} \xrightarrow{\psi} \widetilde H_1(X) \xrightarrow{\partial} \underbrace{\widetilde H_0(U \cap V)}_{\cong \mathbb{Z}} \to \underbrace{\widetilde H_0(U) \oplus \widetilde H_0(V)}_{= 0}.`
So the connecting map $`\partial` is surjective, hence $`\operatorname{img}\partial \cong \mathbb{Z}`, while $`\ker\partial \cong \operatorname{img}\psi \cong \mathbb{Z}` by what we knew about $`\operatorname{img}\phi`.
The splitting lemma below then gives a short exact sequence $`0 \to \mathbb{Z} \to \widetilde H_1(X) \to \mathbb{Z} \to 0`, whose only possibility is $`\widetilde H_1(X) \cong \mathbb{Z} \oplus \mathbb{Z}`.
::::

:::REMARK
Earlier, we remarked (without proof) that $`\pi_2(X)` is trivial — that is, homotopy does not find any "$`2`-dimensional holes" in the torus.
Why is it that $`H_2(X) \cong \mathbb{Z}`?
If you trace the "left, down, left" preimage of $`z_1 - z_2` under $`\partial` back to an element of $`C_2(X)`, the result should be _the whole torus_!
:::

Which emphasizes the point:

:::MORAL
A "hole" detected by homology need not look like the interior of $`S^n`.
:::

Note that the previous example is of a different attitude than the previous ones, because we had to figure out what the maps in the long exact sequence actually were to even compute the groups.
In principle, you could also figure out all the isomorphisms in the previous proof and explicitly compute the generators of $`\widetilde H_1(S^1 \times S^1)`, but to avoid getting bogged down in detail I won't do so here.

Finally, to fully justify the last step, we present:

:::LEMMA "Splitting lemma"
For a short exact sequence $`0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0` of abelian groups, the following are equivalent:

1. There exists $`p \colon B \to A` such that $`A \xrightarrow{f} B \xrightarrow{p} A` is the identity.
2. There exists $`s \colon C \to B` such that $`C \xrightarrow{s} B \xrightarrow{g} C` is the identity.
3. There is an isomorphism from $`B` to $`A \oplus C` compatible with the obvious maps.

In particular, (b) holds anytime $`C` is free.
:::

:::figure "figures/homology/longexact-splitting-biproduct.svg"
A split short exact sequence exhibits $`B \cong A \oplus C`.
:::

In these cases we say the short exact sequence *splits*.
The point is that

:::MORAL
An exact sequence which splits let us obtain $`B` given $`A` and $`C`.
:::

In particular, for $`C = \mathbb{Z}` or any free abelian group, condition (b) is necessarily true.
So, once we obtained the short exact sequence $`0 \to \mathbb{Z} \to \widetilde H_1(X) \to \mathbb{Z} \to 0`, we were done.

:::aside
The splitting lemma is Mathlib's {name}`CategoryTheory.ShortComplex.Splitting`: a splitting of a short complex is exactly the retraction/section data of clauses (a) and (b), and it exhibits the middle object as the biproduct $`A \oplus C` of clause (c).

```lean
example {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) : Type _ :=
  S.Splitting
```
:::

:::REMARK
Unfortunately, not all exact sequences split.
An example of a short exact sequence which doesn't split is $$`0 \to \mathbb{Z}/2 \xhookrightarrow{\times 2} \mathbb{Z}/4 \twoheadrightarrow \mathbb{Z}/2 \to 0`
since it is not true that $`\mathbb{Z}/4 \cong \mathbb{Z}/2 \oplus \mathbb{Z}/2`.
:::

:::REMARK
The splitting lemma is true in any abelian category.
The "direct sum" is the colimit of the two objects $`A` and $`C`.
:::

# Problems

:::PROBLEM "Homology of spheres"
Complete the proof of the homology-of-spheres theorem, i.e. compute $`H_n(S^m)` for all $`m` and $`n`.
(Try doing $`m = 2` first, and you'll see how to proceed.)
(Hint: induction on $`m`, using hemispheres.)
:::

:::PROBLEM "Punctured Euclidean space"
Compute the reduced homology groups of $`\mathbb{R}^n` with $`p \ge 1` points removed.
(Hint: one strategy is induction on $`p`, with base case $`p = 1`.
Another strategy is to let $`U` be the desired space and let $`V` be the union of $`p` non intersecting balls.)
:::

:::PROBLEM "A local relative homology"
Let $`n \ge 1` and $`k \ge 0` be integers.
Compute $`H_k(\mathbb{R}^n, \mathbb{R}^n \setminus \{0\})`.
(Hint: use the relative long exact sequence.
Note that $`\mathbb{R}^n \setminus \{0\}` is homotopy equivalent to $`S^{n-1}`.)
:::

::::PROBLEM "Nine lemma"
Consider a commutative $`3 \times 3` diagram in which all rows are exact and two of the columns are exact.

:::figure "figures/homology/longexact-nine-lemma.svg"
A commutative $`3 \times 3` diagram with exact rows and columns.
:::

Show that the third column is exact as well.
(Hint: $`0 \to A_\bullet \to B_\bullet \to C_\bullet \to 0` is a short exact sequence of chain complexes.
Write out the corresponding long exact sequence.
Nearly all terms will vanish.)
::::

:::PROBLEM "Klein bottle"
Show that the reduced homology groups of the Klein bottle $`K` are given by $$`\widetilde H_n(K) = \begin{cases} \mathbb{Z} \oplus \mathbb{Z}/2 & n = 1 \\ 0 & \text{otherwise}. \end{cases}`
(Hint: it's possible to use two cylinders with $`U` and $`V`.
This time the matrix is $`\begin{bmatrix} 1 & 1 \\ 1 & -1 \end{bmatrix}` or some variant; in particular, it's injective, so $`\widetilde H_2(X) = 0`.)
:::

:::PROBLEM "Triple long exact sequence"
Let $`A \subseteq B \subseteq X` be subspaces.
Show that there is a long exact sequence $$`\dots \to H_n(B, A) \to H_n(X, A) \to H_n(X, B) \to H_{n-1}(B, A) \to \dots.`
(Hint: find a new short exact sequence to apply the long-exact-sequence theorem to.)
:::
